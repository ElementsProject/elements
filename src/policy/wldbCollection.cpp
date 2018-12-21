//Pure virtual base class for a mongodb whitelist database collection.
//Concrete derived classes must define the _name variable. 
//See e.g. wldbWhitelist.cpp
#include "wldbCollection.hpp"
#include <stdexcept>

wldbCollection::wldbCollection(){;}

wldbCollection::wldbCollection(std::string name){
  boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
  _name=name;
}

wldbCollection::~wldbCollection(){
  boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
  delete _collection;
  delete _cursor;
}

void wldbCollection::init(std::string username,
        std::string password,
        std::string port,
        std::string host,
        std::string database,
        std::string authSource,
        std::string authMechanism){
  boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
  whitelistDB::init(username,password,port,host,database,authSource,authMechanism);
  initCollection();
  initCursor();
}

void wldbCollection::initCollection(){
  boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
  delete _collection;
  //Copy the collection object from the database
  collectionName();
  _collection = new mongocxx::collection(*whitelistDB::getCollection(_collectionName));
}

void wldbCollection::initCursor(){
  boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
  delete _cursor;
  _cursor = new mongocxx::cursor(_collection->find({}));
}


void wldbCollection::print(){
  boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
  for(auto doc : (*_cursor)) {
    std::cout << bsoncxx::to_json(doc) << "\n";
  }
}

void wldbCollection::begin(){
  boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
  initCursor();
}

//Read the keys from the database into the policy list.
void wldbCollection::read(){
  boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
  begin();
  for(const bsoncxx::document::view doc : (*_cursor)){
    readAddressesKeys(&doc);
  }
}

void wldbCollection::readAddressesKeys(const bsoncxx::v_noabi::document::view* doc){
    boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
    bsoncxx::document::element addEl=(*doc)["addresses"];
    bsoncxx::document::element keyEl=(*doc)["keys"]; 
    
    //Return if one or both arrays are empty/invalid.
    if(!addEl || !keyEl) return;

    bsoncxx::array::view subarr_add{addEl.get_array().value};
    bsoncxx::array::view subarr_key{keyEl.get_array().value};
    
  //Add all the keys in the subarrays to the policy list
    auto it_add=subarr_add.begin();
    auto it_key=subarr_key.begin();
    while(it_add != subarr_add.end() &&
        it_key != subarr_key.end()){
      _plist->add_derived(
        it_add->get_utf8().value.to_string(),
        it_key->get_utf8().value.to_string()
      );     
      it_add++;
      it_key++;
    }
}

void wldbCollection::deleteAddresses(const bsoncxx::v_noabi::document::view* doc){
    boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
    bsoncxx::array::view subarr_add{(*doc)["addresses"].get_array().value};

  //Add all the keys in the subarrays to the policy list
    auto it_add=subarr_add.begin();
    while(true){
      _plist->delete_address(
        it_add->get_utf8().value.to_string()
      );     
      it_add++;
    }
}

void wldbCollection::watch(){
    boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
    mongocxx::options::change_stream options;
    // Wait up to 1 second before polling again.                                                                          
    const std::chrono::milliseconds await_time{1000};
    options.max_await_time(await_time);

    mongocxx::change_stream stream = _collection->watch(options);

    while (true) {
      for (const bsoncxx::v_noabi::document::view event : stream) {
        processEvent(event);
      }
    }
}

//Process the event this->_event, and update the policy list plist accordingly.
void wldbCollection::processEvent(const bsoncxx::v_noabi::document::view event){
  boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
  std::cout << bsoncxx::to_json(event) << std::endl;
  std::string opType = event["operationType"].get_utf8().value.to_string();

  if(opType == _insertOpType){
    //A new document was inserted. Read the addresses/keys     
     bsoncxx::document::view  doc = event["fullDocument"].get_document().view();
     readAddressesKeys(&doc);
     return;
  }
  
  if(opType == _updateOpType || opType == _deleteOpType){
    resync();
  }

    //The below segment could be of use if we decide to store document id along with addresses.
    /*
    bsoncxx::document::element upDes=event["updateDescription"];
    //Get the updated fields
    bsoncxx::document::element updFields=upDes["updatedFields"];
    //If the fields are valid, read the addresses and keys
    if(updFields){
     if(updFields.length()>0){
        if(updFields["addresses"]){
          if(updFields["keys"]){

          }
        }
      }
    }

    //Get the removed fields
    bsoncxx::array::view remFields=upDes["removedFields"].get_array();
    //If the fields are valid, remove the addresses
     if(remFields.length()>0){
        for (auto fieldName : remFields){
          std::string fName = fieldName.get_utf8().value.to_string();
          if(fName==std::string("addresses") || fName==std::string("keys")){
            //The change stream does not tell us which addresses, if any, have been deleted. 
            //Clear and reread the entire database. TODOLD?
            _plist->clear();
            read();
            break;
          }
        }
      }
      */
  
  //Are there any other operation types? TODOLD
  throw std::runtime_error("Unknown mongodb change_stream event.");
}

//Resync the modified database with the policylist.
void wldbCollection::resync(){
    //Block access from other threads during resync.
    _plist->lock();
    //Reread the database and unlock.
    _plist->clear();
    read();
    _plist->unlock();
    return;
}



