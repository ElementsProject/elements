#pragma once
//A collection
#include "whitelistDB.hpp"
#include "policyList.hpp"
#include <pthread.h>

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

  //Set the policy list that will be updated by this collection
  void policyList(CPolicylist* plist){
    _plist=plist;
  }

  void read(CPolicylist* plist){
    policyList(plist);
    read();
  }

  void read();

  void watch(CPolicylist* plist){
    policyList(plist);
    watch();
  }

  void watch();

  void stopWatch();

protected:
  std::string _name;

  //Change stream event operation types
  const std::string _updateOpType = "update";
  const std::string _insertOpType = "insert";
  const std::string _deleteOpType = "delete";
    
  //Change stream event processor
  void processEvent(const bsoncxx::v_noabi::document::view event);

  //Pointer to the policy list to be updated by this collection
  CPolicylist* _plist;

private:
  //boost::recursive_mutex _mtx;

  wldbCollection();
  whitelistDB* _db;

  mongocxx::collection* _collection = nullptr;
  mongocxx::cursor* _cursor = nullptr;

  
  //Move the cursor to the first document
  void begin();
    
  void initCollection();
  void initCursor();

  void readAddressesKeys(const bsoncxx::v_noabi::document::view* doc);
  void deleteAddresses(const bsoncxx::v_noabi::document::view* doc);

};
