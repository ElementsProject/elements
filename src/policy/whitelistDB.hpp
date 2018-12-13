//A class for interfacting with the whitelist mongodb database.

#include <cstdint>
#include <iostream>
#include <vector>
#include <string>
#include <cstdlib>

#include <bsoncxx/array/view.hpp>
#include <bsoncxx/array/view.hpp>
#include <bsoncxx/builder/basic/array.hpp>
#include <bsoncxx/builder/basic/document.hpp>
#include <bsoncxx/builder/basic/kvp.hpp>
#include <bsoncxx/document/value.hpp>
#include <bsoncxx/document/view.hpp>
#include <bsoncxx/json.hpp>
#include <bsoncxx/stdx/string_view.hpp>
#include <bsoncxx/string/to_string.hpp>
#include <bsoncxx/types.hpp>
#include <bsoncxx/types/value.hpp>


#include <bsoncxx/json.hpp>
#include <bsoncxx/types.hpp>
#include <bsoncxx/types/value.hpp>
#include <bsoncxx/builder/stream/array.hpp>
#include <bsoncxx/builder/stream/document.hpp>
#include <mongocxx/client.hpp>
#include <mongocxx/pool.hpp>
#include <mongocxx/instance.hpp>
#include <mongocxx/stdx.hpp>
#include <mongocxx/uri.hpp>
#include <mongocxx/database.hpp>
#include <mongocxx/collection.hpp>

using bsoncxx::builder::stream::close_array;
using bsoncxx::builder::stream::close_document;
using bsoncxx::builder::stream::document;
using bsoncxx::builder::stream::finalize;
using bsoncxx::builder::stream::open_array;
using bsoncxx::builder::stream::open_document;


class whitelistDB{
public:
  //Returns the instance of whitelistDB, instantiating first if necessary.
  static whitelistDB* getInstance(std::string username = std::getenv("MONGODB_USER"),
        std::string password = std::getenv("MONGODB_PASS"),
        std::string port     = std::getenv("MONGODB_PORT"),
        std::string host     = "mongodbhost",
        std::string database = std::getenv("MONGODB_USER"),
        std::string authSource = std::getenv("MONGODB_USER"),
        std::string authMechanism = "SCRAM-SHA-256");
  ~whitelistDB();
  void init();

  mongocxx::collection* getCollection(std::string name);

private:
  static whitelistDB* _instance;
  whitelistDB(std::string username ,
	      std::string password,
	      std::string port,
	      std::string host,
	      std::string database,
	      std::string authSource,
	      std::string authMechanism);

  mongocxx::instance _mongo_instance{};
  std::string _s_username="";
  std::string _s_password="";
  std::string _s_port="";
  std::string _s_host="";
  std::string _s_database="";
  std::string _s_authSource="";
  std::string _s_authMechanism="";

  void initUri();
  void initPool();
  void initDatabase();

  mongocxx::uri* _uri = nullptr;
  mongocxx::pool* _pool = nullptr;
  mongocxx::database* _database = nullptr;    
};
