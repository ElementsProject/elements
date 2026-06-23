// Copyright (c) 2009-2018 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include <qt/test/uritests.h>

#include <qt/guiutil.h>
#include <qt/walletmodel.h>

#include <QUrl>

void URITests::uriTests()
{
    // liquid URI tests
    g_con_elementsmode = true;
    SendCoinsRecipient info{"lq1qq0ha4ml3dsqexnkdssskvt203kl54xj5zxt9sfwgzpy7unf49aagslltf4k7pqjtwk4j8emny0k8vppj88k0z9pa4y0mwfzyu", "label", 100000000, "message"};
    QString liquid_uri = GUIUtil::formatBitcoinURI(info);
    QVERIFY(liquid_uri.split(":")[0] == "liquidnetwork");

    SendCoinsRecipient rcv;
    QVERIFY(GUIUtil::parseBitcoinURI(liquid_uri, &rcv));
    QVERIFY(rcv.address == QString("lq1qq0ha4ml3dsqexnkdssskvt203kl54xj5zxt9sfwgzpy7unf49aagslltf4k7pqjtwk4j8emny0k8vppj88k0z9pa4y0mwfzyu"));
    QVERIFY(rcv.amount == 100000000);
    QVERIFY(rcv.label == QString("label"));
    QVERIFY(rcv.message == QString("message"));

    // example liquidv1 URI from blockstream app
    QUrl url{QString("liquidnetwork:lq1qq2j9v49hgsgz9s7v7myty50hsy0a6vk6sjmc9z6m0k208njwcllg9dzwk6prxmzy0wzvejc8tdn0fls88x8ksefwdw2l5hym9?assetid=6f0279e9ed041c3d710a9f57d0c02928416460c4b722ae3457a11eec381c526d&amount=1.00000000")};
    QVERIFY(GUIUtil::parseBitcoinURI(url, &rcv));
    QVERIFY(rcv.address == QString("lq1qq2j9v49hgsgz9s7v7myty50hsy0a6vk6sjmc9z6m0k208njwcllg9dzwk6prxmzy0wzvejc8tdn0fls88x8ksefwdw2l5hym9"));
    QVERIFY(rcv.amount == 100000000);
    QVERIFY(rcv.label.isEmpty());
    QVERIFY(rcv.message.isEmpty());

    // example liquid testnet URI from blockstream app
    url.setUrl(QString("liquidtestnet:tlq1qqggjrm7s09agm8vvgsld8sq3a0luppzwyg3fl3rtrl9xcq50n2cny8le5xdl4k7ufxz6m4249njkdvxfzhdax6fczggf8ncjz?assetid=144c654344aa716d6f3abcc1ca90e5641e4e2a7f633bc09fe3baf64585819a49&amount=0.00100000"));
    QVERIFY(GUIUtil::parseBitcoinURI(url, &rcv));
    QVERIFY(rcv.address == QString("tlq1qqggjrm7s09agm8vvgsld8sq3a0luppzwyg3fl3rtrl9xcq50n2cny8le5xdl4k7ufxz6m4249njkdvxfzhdax6fczggf8ncjz"));
    QVERIFY(rcv.amount == 100000);
    QVERIFY(rcv.label.isEmpty());
    QVERIFY(rcv.message.isEmpty());

    // check bitcoin mode
    g_con_elementsmode = false;
    info = SendCoinsRecipient{"175tWpb8K1S7NmH4Zx6rewF9WQrcZv245W", "label", 100000000, "message"};
    QString bitcoin_uri = GUIUtil::formatBitcoinURI(info);
    QVERIFY(bitcoin_uri.split(":")[0] == "bitcoin");
    QVERIFY(GUIUtil::parseBitcoinURI(bitcoin_uri, &rcv));
    QVERIFY(rcv.address == QString("175tWpb8K1S7NmH4Zx6rewF9WQrcZv245W"));
    QVERIFY(rcv.amount == 100000000);
    QVERIFY(rcv.label == QString("label"));
    QVERIFY(rcv.message == QString("message"));

    // Bitcoin URI tests from upstream
    SendCoinsRecipient rv;
    QUrl uri;
    uri.setUrl(QString("bitcoin:175tWpb8K1S7NmH4Zx6rewF9WQrcZv245W?req-dontexist="));
    QVERIFY(!GUIUtil::parseBitcoinURI(uri, &rv));

    uri.setUrl(QString("bitcoin:175tWpb8K1S7NmH4Zx6rewF9WQrcZv245W?dontexist="));
    QVERIFY(GUIUtil::parseBitcoinURI(uri, &rv));
    QVERIFY(rv.address == QString("175tWpb8K1S7NmH4Zx6rewF9WQrcZv245W"));
    QVERIFY(rv.label == QString());
    QVERIFY(rv.amount == 0);

    uri.setUrl(QString("bitcoin:175tWpb8K1S7NmH4Zx6rewF9WQrcZv245W?label=Wikipedia Example Address"));
    QVERIFY(GUIUtil::parseBitcoinURI(uri, &rv));
    QVERIFY(rv.address == QString("175tWpb8K1S7NmH4Zx6rewF9WQrcZv245W"));
    QVERIFY(rv.label == QString("Wikipedia Example Address"));
    QVERIFY(rv.amount == 0);

    uri.setUrl(QString("bitcoin:175tWpb8K1S7NmH4Zx6rewF9WQrcZv245W?amount=0.001"));
    QVERIFY(GUIUtil::parseBitcoinURI(uri, &rv));
    QVERIFY(rv.address == QString("175tWpb8K1S7NmH4Zx6rewF9WQrcZv245W"));
    QVERIFY(rv.label == QString());
    QVERIFY(rv.amount == 100000);

    uri.setUrl(QString("bitcoin:175tWpb8K1S7NmH4Zx6rewF9WQrcZv245W?amount=1.001"));
    QVERIFY(GUIUtil::parseBitcoinURI(uri, &rv));
    QVERIFY(rv.address == QString("175tWpb8K1S7NmH4Zx6rewF9WQrcZv245W"));
    QVERIFY(rv.label == QString());
    QVERIFY(rv.amount == 100100000);

    uri.setUrl(QString("bitcoin:175tWpb8K1S7NmH4Zx6rewF9WQrcZv245W?amount=100&label=Wikipedia Example"));
    QVERIFY(GUIUtil::parseBitcoinURI(uri, &rv));
    QVERIFY(rv.address == QString("175tWpb8K1S7NmH4Zx6rewF9WQrcZv245W"));
    QVERIFY(rv.amount == 10000000000LL);
    QVERIFY(rv.label == QString("Wikipedia Example"));

    uri.setUrl(QString("bitcoin:175tWpb8K1S7NmH4Zx6rewF9WQrcZv245W?message=Wikipedia Example Address"));
    QVERIFY(GUIUtil::parseBitcoinURI(uri, &rv));
    QVERIFY(rv.address == QString("175tWpb8K1S7NmH4Zx6rewF9WQrcZv245W"));
    QVERIFY(rv.label == QString());

    QVERIFY(GUIUtil::parseBitcoinURI("bitcoin:175tWpb8K1S7NmH4Zx6rewF9WQrcZv245W?message=Wikipedia Example Address", &rv));
    QVERIFY(rv.address == QString("175tWpb8K1S7NmH4Zx6rewF9WQrcZv245W"));
    QVERIFY(rv.label == QString());

    uri.setUrl(QString("bitcoin:175tWpb8K1S7NmH4Zx6rewF9WQrcZv245W?req-message=Wikipedia Example Address"));
    QVERIFY(GUIUtil::parseBitcoinURI(uri, &rv));

    // Commas in amounts are not allowed.
    uri.setUrl(QString("bitcoin:175tWpb8K1S7NmH4Zx6rewF9WQrcZv245W?amount=1,000&label=Wikipedia Example"));
    QVERIFY(!GUIUtil::parseBitcoinURI(uri, &rv));

    uri.setUrl(QString("bitcoin:175tWpb8K1S7NmH4Zx6rewF9WQrcZv245W?amount=1,000.0&label=Wikipedia Example"));
    QVERIFY(!GUIUtil::parseBitcoinURI(uri, &rv));

    // There are two amount specifications. The last value wins.
    uri.setUrl(QString("bitcoin:175tWpb8K1S7NmH4Zx6rewF9WQrcZv245W?amount=100&amount=200&label=Wikipedia Example"));
    QVERIFY(GUIUtil::parseBitcoinURI(uri, &rv));
    QVERIFY(rv.address == QString("175tWpb8K1S7NmH4Zx6rewF9WQrcZv245W"));
    QVERIFY(rv.amount == 20000000000LL);
    QVERIFY(rv.label == QString("Wikipedia Example"));

    // The first amount value is correct. However, the second amount value is not valid. Hence, the URI is not valid.
    uri.setUrl(QString("bitcoin:175tWpb8K1S7NmH4Zx6rewF9WQrcZv245W?amount=100&amount=1,000&label=Wikipedia Example"));
    QVERIFY(!GUIUtil::parseBitcoinURI(uri, &rv));

    // Test label containing a question mark ('?').
    uri.setUrl(QString("bitcoin:175tWpb8K1S7NmH4Zx6rewF9WQrcZv245W?amount=100&label=?"));
    QVERIFY(GUIUtil::parseBitcoinURI(uri, &rv));
    QVERIFY(rv.address == QString("175tWpb8K1S7NmH4Zx6rewF9WQrcZv245W"));
    QVERIFY(rv.amount == 10000000000LL);
    QVERIFY(rv.label == QString("?"));

    // Escape sequences are not supported.
    uri.setUrl(QString("bitcoin:175tWpb8K1S7NmH4Zx6rewF9WQrcZv245W?amount=100&label=%3F"));
    QVERIFY(GUIUtil::parseBitcoinURI(uri, &rv));
    QVERIFY(rv.address == QString("175tWpb8K1S7NmH4Zx6rewF9WQrcZv245W"));
    QVERIFY(rv.amount == 10000000000LL);
    QVERIFY(rv.label == QString("%3F"));
}
