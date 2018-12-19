//Pure virtual base class for a mongodb whitelist database collection.
//Concrete derived classes must define the _name variable. 
//See e.g. wldbWhitelist.cpp
#include "wldbCollection.hpp"

wldbCollection::wldbCollection(std::string name){
  _name=name;
}

wldbCollection::~wldbCollection(){
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
  _db=whitelistDB::getInstance();
  _db->init(username,password,port,host,database,authSource,authMechanism);
  init();
}

void wldbCollection::init(){
  initCollection();
  initCursor();
}

void wldbCollection::initCollection(){
  delete _collection;
  //Copy the collection object from the database
  _collection = new mongocxx::collection(*_db->getCollection(_name));
}

void wldbCollection::initCursor(){
  delete _cursor;
  _cursor = new mongocxx::cursor(_collection->find({}));
}


void wldbCollection::print(){
  for(auto doc : (*_cursor)) {
    std::cout << bsoncxx::to_json(doc) << "\n";
  }
}

void wldbCollection::begin(){
  initCursor();
}

//Read the keys from the database into the policy list.
void wldbCollection::read(CPolicylist* plist){
  begin();
  for(auto doc : (*_cursor)){
    bsoncxx::array::view subarr_add{doc["addresses"].get_array().value};
    bsoncxx::array::view subarr_key{doc["keys"].get_array().value};

    auto it_add=subarr_add.begin();
    auto it_key=subarr_key.begin();
    while(it_add != subarr_add.end() &&
        it_key != subarr_key.end()){
      plist->add_derived(
        it_add->get_utf8().value.to_string(),
        it_key->get_utf8().value.to_string()
      );     
      it_add++;
      it_key++;
    }
  }
}