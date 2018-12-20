#pragma once
//A whitelist mongdo document class.

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

using bsoncxx::builder::stream::close_array;
using bsoncxx::builder::stream::close_document;
using bsoncxx::builder::stream::document;
using bsoncxx::builder::stream::finalize;
using bsoncxx::builder::stream::open_array;
using bsoncxx::builder::stream::open_document;

class wldbDoc{
public:
  wldbDoc(std::string id="", 
	  std::vector<std::string> keys=std::vector<std::string>(),
	  std::vector<std::string> addresses=std::vector<std::string>()
	  );
  ~wldbDoc();

  //Setters
  void id(std::string val){_id=val;}
  void keys(std::vector<std::string> val){_keys=val;}
  void addresses(std::vector<std::string> val){_addresses=val;}

  //Modifiers
  void add_key_address(std::string key, std::string address);

  //Getters
  std::string id() const {return _id;}
  std::vector<std::string> addresses() const {return _addresses;}
  std::vector<std::string> keys() const {return _keys;}

  bsoncxx::document::view view() const {return _view;}

private:
  std::string _id;
  std::vector<std::string> _addresses;
  std::vector<std::string> _keys;

  bsoncxx::document::value* _doc_value = nullptr;
  bsoncxx::document::view _view;
  bsoncxx::document::element _element;

  void build();

};
