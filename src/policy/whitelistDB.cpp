#include "whitelistDB.hpp"

whitelistDB* whitelistDB::_instance = nullptr;

//Returns the one and only instance of whitelistDB, instantiating first if necessary.
whitelistDB* whitelistDB::getInstance(std::string username,
				      std::string password,
				      std::string port,
				      std::string host,
				      std::string database,
				      std::string authSource,
				      std::string authMechanism){
  if (_instance == nullptr){
    _instance = new whitelistDB(username, password, port, host, database, authSource, authMechanism);
  }
  return _instance;
}

whitelistDB::whitelistDB(std::string username,
			 std::string password,
			 std::string port,
			 std::string host,
			 std::string database,
			 std::string authSource,
			 std::string authMechanism){
  _s_username=username;
  _s_password=password;
  _s_port=port;
  _s_host=host;
  _s_database=database;
  _s_authSource=authSource;
  _s_authMechanism=authMechanism;
  init();
}

whitelistDB::~whitelistDB(){
  delete _uri;
  delete _pool;
  delete _database;
}

void whitelistDB::init(){
  initUri();
  initPool();
  initDatabase();
}
									  
void whitelistDB::initUri(){
  std::string uri_string = std::string("mongodb://") + 
    _s_username + std::string(":") + 
    _s_password + std::string("@") + ("mongodbhost:") + 
    _s_port + std::string("/") + 
    _s_database + 
    std::string("?authSource=") + _s_authSource + std::string("&authMechanism=") + _s_authMechanism;
  delete _uri;
  _uri = new mongocxx::uri(uri_string.c_str());
}

void whitelistDB::initPool(){
  delete _pool;
  _pool = new mongocxx::pool(*_uri);
}

void whitelistDB::initDatabase(){
  auto client = _pool->acquire();
  //admin is the default database
  delete _database;
  _database = new  mongocxx::database((*client)[_s_database.c_str()]);
}

mongocxx::collection* whitelistDB::getCollection(std::string name){
  mongocxx::collection* coll = new mongocxx::collection((*_database)[name.c_str()]);
  return coll;
}





