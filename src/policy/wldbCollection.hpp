//A collection
#include "whitelistDB.hpp"
#include "policyList.hpp"

class wldbCollection{
public:
    wldbCollection(std::string name);
    ~wldbCollection();

    void init();
     void init(std::string username,
        std::string password,
        std::string port,
        std::string host,
        std::string database,
        std::string authSource,
        std::string authMechanism);

  void print();

  void read(CPolicylist* plist);

protected:
  std::string _name;
    
private:
  wldbCollection();
  whitelistDB* _db;

  mongocxx::collection* _collection = nullptr;
  mongocxx::cursor* _cursor = nullptr;
  
  //Move the cursor to the first document
  void begin();

  //Key cursors
  bsoncxx::v_noabi::array::view::const_iterator _key_iter;
  bsoncxx::v_noabi::array::view::const_iterator _add_iter;
  bsoncxx::v_noabi::array::view::const_iterator _key_iter_end;
  bsoncxx::v_noabi::array::view::const_iterator _add_iter_end;
    
  void initCollection();
  void initCursor();
};
