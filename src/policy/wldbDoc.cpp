#include "wldbDoc.hpp"

wldbDoc::wldbDoc(std::string id, std::vector<std::string> keys, std::vector<std::string> addresses){
  this->id(id);
  this->keys(keys);
  this->addresses(addresses);
  build();
}

wldbDoc::~wldbDoc(){
  ;
}

void wldbDoc::build(){
  //Build the document
  auto builder1 = bsoncxx::builder::stream::document{};
  builder1
    << "_id" << _id
    << "keys" << bsoncxx::builder::stream::open_array << _keys[0] << _keys[1] 
    << bsoncxx::builder::stream::close_array 
    << bsoncxx::builder::stream::finalize;

  /*
  auto builder2 = bsoncxx::builder::stream::document{};
  for(auto key:_keys){
    builder2 << key;
  }

  auto builder3 = bsoncxx::builder::stream::document{};
  builder3  << bsoncxx::builder::stream::close_array
  builder3  << "addresses" << bsoncxx::builder::stream::open_array;

  auto builder4 = bsoncxx::builder::stream::document{};
  for(auto address:_addresses){
    builder4 << address;
  }

  auto builder5 = bsoncxx::builder::stream::document{};
  builder5 << bsoncxx::builder::stream::close_array
     << bsoncxx::builder::stream::finalize;
  */
  


  delete _doc_value;
  _doc_value = new bsoncxx::document::value(builder1);
}

