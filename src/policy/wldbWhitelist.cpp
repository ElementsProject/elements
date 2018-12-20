#include "wldbWhitelist.hpp"

wldbWhitelist::wldbWhitelist():wldbCollection("whitelist"){
	//boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
}
  
wldbWhitelist::~wldbWhitelist(){
	//boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
}