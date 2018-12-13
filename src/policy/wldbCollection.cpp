#include "wldbCollection.hpp"

wldbCollection::wldbCollection(std::string name){
  _name=name;
  init();
}

wldbCollection::~wldbCollection(){
  delete _collection;
  delete _cursor;
}

void wldbCollection::init(){
  initCollection();
  initCursor();
}

void wldbCollection::initCollection(){
  delete _collection;
  _db=whitelistDB::getInstance();
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

//Each call to "begin" checks for newly created documents.
//In mongdbcxx, each call to begin (confusingly) iterates to the next document, 
//instead of going to the beginning document.
//Therefore, to actually go to the beginning we need to recreate the cursors.
void wldbCollection::begin(){
  initCursor();
}

wldbCollection::status wldbCollection::next_address_key
                      (std::vector<std::string>& pair){
  pair.clear();
  if( ++_add_iter != _add_iter_end &&
      ++_key_iter != _key_iter_end ){
    ;
  } else {
      auto doc=_cursor->begin();
        if(doc == _cursor->end()) {
        //No more docs left to read.
        return wldbCollection::status::END;
      } else {

     bsoncxx::array::view subarr_add{(*doc)["addresses"].get_array().value};
     bsoncxx::array::view subarr_key{(*doc)["keys"].get_array().value};

      _add_iter=subarr_add.begin();
      _add_iter_end=subarr_add.end();

      _key_iter=subarr_key.begin();
      _key_iter_end=subarr_key.end();
      }
    

    }
      
    

  pair.push_back((*_add_iter).get_utf8().value.to_string());
  pair.push_back((*_key_iter).get_utf8().value.to_string());
  return wldbCollection::status::SUCCESS;
}

wldbCollection::status wldbCollection::first_address_key(std::vector<std::string>& pair){
  begin();
  return next_address_key(pair);
}

