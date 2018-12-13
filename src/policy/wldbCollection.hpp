//A collection
#include "whitelistDB.hpp"

class wldbCollection{
public:
  wldbCollection(std::string name);
  ~wldbCollection();

  void init();
  void print();


  enum status{
    SUCCESS, END
  };

  wldbCollection::status first_address_key(std::vector<std::string>& keypair); 
  wldbCollection::status next_address_key(std::vector<std::string>& keypair); 


protected:
  std::string _name;
  wldbCollection();
  
private:

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
