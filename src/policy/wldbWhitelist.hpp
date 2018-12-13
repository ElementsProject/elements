//The one and only  mongodb "whitelist" collection.
#include "wldbCollection.hpp"

class wldbWhitelist: public wldbCollection{
public:
  ~wldbWhitelist();
  static wldbWhitelist* getInstance();
  
private:
  wldbWhitelist();
  static wldbWhitelist* _instance;
};
