//The one and only  mongodb "whitelist" collection.
#pragma once

#include "wldbCollection.hpp"

class wldbWhitelist: public wldbCollection{
public:
  wldbWhitelist();
  ~wldbWhitelist();

private:
  //boost::recursive_mutex _mtx;
};
