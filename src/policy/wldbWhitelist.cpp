#include "wldbWhitelist.hpp"

wldbWhitelist* wldbWhitelist::_instance = nullptr;

wldbWhitelist* wldbWhitelist::getInstance(){
		  if(_instance == nullptr){
    _instance =  new wldbWhitelist();
  }
  return _instance;
}

wldbWhitelist::wldbWhitelist():wldbCollection("whitelist"){
	//boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
}
  
wldbWhitelist::~wldbWhitelist(){
	//boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
  	delete _instance;
}