//The one and only  mongodb "whitelist" collection.
#include "wldbCollection.hpp"

class wldbWhitelist: public wldbCollection{
public:
  wldbWhitelist();
  ~wldbWhitelist();
  static wldbWhitelist* getInstance();

private:
  static wldbWhitelist* _instance;
};
