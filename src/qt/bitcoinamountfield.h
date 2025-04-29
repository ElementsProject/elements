// Copyright (c) 2011-2021 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#ifndef BITCOIN_QT_BITCOINAMOUNTFIELD_H
#define BITCOIN_QT_BITCOINAMOUNTFIELD_H

#include <asset.h>
#include <consensus/amount.h>
#include <qt/bitcoinunits.h>

#include <set>
#include <QWidget>

class AmountSpinBox;

QT_BEGIN_NAMESPACE
class QComboBox;
QT_END_NAMESPACE

/** Widget for entering bitcoin amounts.
  */
class BitcoinAmountField: public QWidget
{
    Q_OBJECT

    // ugly hack: for some unknown reason CAmount (instead of qint64) does not work here as expected
    // discussion: https://github.com/bitcoin/bitcoin/pull/5117
    Q_PROPERTY(qint64 value READ value WRITE setValue NOTIFY valueChanged USER true)

public:
    explicit BitcoinAmountField(std::set<CAsset> allowed_assets, QWidget *parent = nullptr);
    explicit BitcoinAmountField(QWidget *parent = nullptr);

    std::pair<CAsset, CAmount> fullValue(bool *valid = nullptr) const;
    void setFullValue(const CAsset& asset, const CAmount& value);

    CAmount value(bool *value=nullptr) const;
    void setValue(const CAmount& value);

    /** If allow empty is set to false the field will be set to the minimum allowed value if left empty. **/
    void SetAllowEmpty(bool allow);

    /** Set the minimum value in satoshis **/
    void SetMinValue(const CAmount& value);

    /** Set the maximum value in satoshis **/
    void SetMaxValue(const CAmount& value);

    /** Set single step in satoshis **/
    void setSingleStep(const CAmount& step);

    /** Make read-only **/
    void setReadOnly(bool fReadOnly);

    /** Mark current value as invalid in UI. */
    void setValid(bool valid);
    /** Perform input validation, mark field as invalid if entered value is not valid. */
    bool validate();

    void setAllowedAssets(const std::set<CAsset>& allowed_assets);

    /** Change unit used to display amount. */
    void setDisplayUnit(const CAsset&);
    void setDisplayUnit(BitcoinUnit new_unit);

    /** Make field empty and ready for new input. */
    void clear();

    /** Enable/Disable. */
    void setEnabled(bool fEnabled);

    /** Qt messes up the tab chain by default in some cases (issue https://bugreports.qt-project.org/browse/QTBUG-10907),
        in these cases we have to set it up manually.
    */
    QWidget *setupTabChain(QWidget *prev);

Q_SIGNALS:
    void valueChanged();

protected:
    /** Intercept focus-in event and ',' key presses */
    bool eventFilter(QObject *object, QEvent *event) override;

private:
    std::set<CAsset> m_allowed_assets;
    CAsset asset;
    AmountSpinBox* amount{nullptr};
    QComboBox *unit;

    bool hasAssetChoice(const CAsset&) const;
    void addAssetChoice(const CAsset&);
    void removeAssetChoice(const CAsset&);

private Q_SLOTS:
    void unitChanged(int idx);

};

#endif // BITCOIN_QT_BITCOINAMOUNTFIELD_H
