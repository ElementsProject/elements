// Copyright (c) 2018 The CommerceBlock Developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#pragma once
//A class for interfacting with the whitelist mongodb database.

#include <cstdint>
#include <iostream>
#include <vector>
#include <string>
#include <cstdlib>

#include <bsoncxx/array/view.hpp>
#include <bsoncxx/array/view.hpp>
#include <bsoncxx/builder/basic/array.hpp>
#include <bsoncxx/builder/basic/document.hpp>
#include <bsoncxx/builder/basic/kvp.hpp>
#include <bsoncxx/document/value.hpp>
#include <bsoncxx/document/view.hpp>
#include <bsoncxx/json.hpp>
#include <bsoncxx/stdx/string_view.hpp>
#include <bsoncxx/string/to_string.hpp>
#include <bsoncxx/types.hpp>
#include <bsoncxx/types/value.hpp>


#include <bsoncxx/json.hpp>
#include <bsoncxx/types.hpp>
#include <bsoncxx/types/value.hpp>
#include <bsoncxx/builder/stream/array.hpp>
#include <bsoncxx/builder/stream/document.hpp>
#include <mongocxx/client.hpp>
#include <mongocxx/pool.hpp>
#include <mongocxx/instance.hpp>
#include <mongocxx/stdx.hpp>
#include <mongocxx/uri.hpp>
#include <mongocxx/database.hpp>
#include <mongocxx/collection.hpp>

#include <boost/thread/recursive_mutex.hpp>

#include "policyList.hpp"

using bsoncxx::builder::stream::close_array;
using bsoncxx::builder::stream::close_document;
using bsoncxx::builder::stream::document;
using bsoncxx::builder::stream::finalize;
using bsoncxx::builder::stream::open_array;
using bsoncxx::builder::stream::open_document;


class policyListDatabase{
public:
  policyListDatabase();
  ~policyListDatabase();
  void init(std::string username,
        std::string password,
        std::string port,
        std::string host,
        std::string database,
        std::string authSource,
        std::string authMechanism);

  mongocxx::collection* getCollection();

  void print();

  //Set the policy list that will be updated by this collection
  void setPolicyList(CPolicyList* plist){
    _plist=plist;
  }

  void read(CPolicyList* plist){
    setPolicyList(plist);
    read();
  }

  virtual void read() = 0;

  void watch(CPolicyList* plist){
    setPolicyList(plist);
    watch();
  }

  void watch();

  void stopWatch();

protected:
	 boost::recursive_mutex _mtx;
  //Concrete classes must override this method to specify the collection name: 
  //"whitelist", "freezelist", "burnlist", etc.
  virtual void collectionName() = 0;  
  std::string _collectionName="";
  virtual void readAddressesKeys(const bsoncxx::v_noabi::document::view* doc) = 0;


  //Change stream event operation types
  const std::string _updateOpType = "update";
  const std::string _insertOpType = "insert";
  const std::string _deleteOpType = "delete";
    
  //Change stream event processor
  virtual void processEvent(const bsoncxx::v_noabi::document::view event);

  //Pointer to the policy list to be updated by this collection
  CPolicyList* _plist;

  mongocxx::collection* _collection = nullptr;
  mongocxx::cursor* _cursor = nullptr;
  
  //Move the cursor to the first document
  void begin();

private:

  mongocxx::instance _mongo_instance{};
  std::string _s_username="";
  std::string _s_password="";
  std::string _s_port="";
  std::string _s_host="";
  std::string _s_database="";
  std::string _s_authSource="";
  std::string _s_authMechanism="";

  void initUri();
  void initPool();
  void initDatabase();

  mongocxx::uri* _uri = nullptr;
  mongocxx::pool* _pool = nullptr;
  mongocxx::database* _database = nullptr;  


    
  void initCollection();
  void initCursor();

  void deleteAddresses(const bsoncxx::v_noabi::document::view* doc);

  void resync();

};