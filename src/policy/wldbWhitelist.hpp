//The one and only  mongodb "whitelist" collection.
#include "wldbCollection.hpp"

class wldbWhitelist: public wldbCollection{
public:
	boost::recursive_mutex _mtx;
  wldbWhitelist();
  ~wldbWhitelist();
  static wldbWhitelist* getInstance();

private:
  static wldbWhitelist* _instance;
};
