// Copyright (c) 2018 The CommerceBlock Developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include "policyListDatabase.hpp"
#include <sstream>

policyListDatabase::policyListDatabase(){
  boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
}

policyListDatabase::~policyListDatabase(){
  boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
  delete _uri;
  delete _pool;
  delete _database;
  delete _collection;
  delete _cursor;
}

void policyListDatabase::init(std::string username,
        std::string password,
        std::string port,
        std::string host,
        std::string database,
        std::string authSource,
        std::string authMechanism){
  boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
  _s_username=username;
  _s_password=password;
  _s_port=port;
  _s_host=host;
  _s_database=database;
  _s_authSource=authSource;
  _s_authMechanism=authMechanism;

  initUri();
  initPool();
  initDatabase();
  initCollection();
  initCursor();
}
									  
void policyListDatabase::initUri(){
  boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
  std::stringstream ss;
  ss << std::string("mongodb://");
  if(_s_username.length()>0){ 
    ss << _s_username << std::string(":") << 
    _s_password << std::string("@");
  }
  ss << _s_host << (":") << 
  _s_port << std::string("/") << 
  _s_database;
  if(_s_username.length()>0 && _s_authSource.length()>0){ 
    ss << std::string("?authSource=") <<
    _s_authSource << std::string("&authMechanism=") << _s_authMechanism;
  }
   delete _uri;
  _uri = new mongocxx::uri(ss.str().c_str());
}

void policyListDatabase::initPool(){
  boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
  delete _pool;
  _pool = new mongocxx::pool(*_uri);
}

void policyListDatabase::initDatabase(){
  boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
  auto client = _pool->acquire();
  //admin is the default database
  delete _database;
  _database = new  mongocxx::database((*client)[_s_database.c_str()]);
}

mongocxx::collection* policyListDatabase::getCollection(){
  boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
  mongocxx::collection* coll = new mongocxx::collection((*_database)[_collectionName.c_str()]);
  return coll;
}

void policyListDatabase::initCollection(){
  boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
  delete _collection;
  //Copy the collection object from the database
  collectionName();
  _collection = new mongocxx::collection(*getCollection());
}

void policyListDatabase::initCursor(){
  boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
  delete _cursor;
  _cursor = new mongocxx::cursor(_collection->find({}));
}


void policyListDatabase::print(){
  boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
  for(auto doc : (*_cursor)) {
    std::cout << bsoncxx::to_json(doc) << "\n";
  }
}

void policyListDatabase::begin(){
  boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
  initCursor();
}


void policyListDatabase::deleteAddresses(const bsoncxx::v_noabi::document::view* doc){
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

void policyListDatabase::watch(){
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
void policyListDatabase::processEvent(const bsoncxx::v_noabi::document::view event){
  boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
  //std::cout << bsoncxx::to_json(event) << std::endl;
  std::string opType = event["operationType"].get_utf8().value.to_string();

  if(opType == _insertOpType){
    //A new document was inserted. Read the addresses/keys     
     bsoncxx::document::view  doc = event["fullDocument"].get_document().view();
     readAddressesKeys(&doc);
  } else if(opType == _updateOpType){
    synchronise();
  }else if(opType == _deleteOpType){
    synchronise();
  } else {
  //Are there any other operation types? TODOLD
  throw std::runtime_error(std::string(__func__) + 
    ": unknown mongodb change_stream event: " +
    opType);
  }
  return;
}


