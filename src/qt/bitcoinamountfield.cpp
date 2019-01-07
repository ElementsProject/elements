// Copyright (c) 2011-2018 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include <qt/bitcoinamountfield.h>

#include <qt/bitcoinunits.h>
#include <qt/guiconstants.h>
#include <qt/qvaluecombobox.h>
#include "guiutil.h"

#include "assetsdir.h"
#include "chainparams.h"

#include <QApplication>
#include <QAbstractSpinBox>
#include <QHBoxLayout>
#include <QKeyEvent>
#include <QLineEdit>

Q_DECLARE_METATYPE(CAsset)

/** QSpinBox that uses fixed-point numbers internally and uses our own
 * formatting/parsing functions.
 */
class AmountSpinBox: public QAbstractSpinBox
{
    Q_OBJECT

public:
    explicit AmountSpinBox(QWidget *parent):
        QAbstractSpinBox(parent),
        currentUnit(BitcoinUnits::BTC),
        singleStep(0)
    {
        current_asset = Params().GetConsensus().pegged_asset;

        setAlignment(Qt::AlignRight);

        connect(lineEdit(), &QLineEdit::textEdited, this, &AmountSpinBox::valueChanged);
    }

    QValidator::State validate(QString &text, int &pos) const
    {
        if(text.isEmpty())
            return QValidator::Intermediate;
        bool valid = false;
        parse(text, &valid);
        /* Make sure we return Intermediate so that fixup() is called on defocus */
        return valid ? QValidator::Intermediate : QValidator::Invalid;
    }

    void fixup(QString &input) const
    {
        bool valid = false;
        CAmount val = parse(input, &valid);
        if(valid)
        {
            input = GUIUtil::formatAssetAmount(current_asset, val, currentUnit, BitcoinUnits::separatorAlways, false);
            lineEdit()->setText(input);
        }
    }

    int currentPeggedUnit() const
    {
        assert(current_asset == Params().GetConsensus().pegged_asset);
        return currentUnit;
    }

    std::pair<CAsset, CAmount> value(bool *valid_out=0) const
    {
        return std::make_pair(current_asset, parse(text(), valid_out));
    }

    void setValue(const CAsset& asset, CAmount value)
    {
        current_asset = asset;
        lineEdit()->setText(GUIUtil::formatAssetAmount(asset, value, currentUnit, BitcoinUnits::separatorAlways, false));
        Q_EMIT valueChanged();
    }

    inline void setValue(const std::pair<CAsset, CAmount>& value)
    {
        setValue(value.first, value.second);
    }


    void stepBy(int steps)
    {
        bool valid = false;
        auto val = value(&valid);
        CAmount currentSingleStep = singleStep;
        if (!currentSingleStep) {
            if (current_asset == Params().GetConsensus().pegged_asset) {
                currentSingleStep = 100000;  // satoshis
            } else {
                currentSingleStep = 100000000;  // a whole asset
            }
        }
        val.second = val.second + steps * singleStep;
        val.second = qMax(val.second, CAmount(0));
        if (val.first == Params().GetConsensus().pegged_asset) {
            val.second = qMin(val.second, BitcoinUnits::maxMoney());
        }
        setValue(val);
    }

    void setDisplayUnit(const CAsset& asset)
    {
        if (asset == Params().GetConsensus().pegged_asset) {
            setDisplayUnit(currentUnit);
            return;
        }

        // Only used for bitcoins -> other asset
        // Leave the number alone, since the user probably intended it for this asset

        current_asset = asset;
        Q_EMIT valueChanged();
    }

    void setDisplayUnit(int unit)
    {
        bool valid = false;
        std::pair<CAsset, CAmount> val = value(&valid);
        const bool was_pegged = (val.first == Params().GetConsensus().pegged_asset);

        current_asset = Params().GetConsensus().pegged_asset;
        currentUnit = unit;

        if (!was_pegged) {
            // Leave the text as-is, if it's valid
            value(&valid);
            if (valid) {
                Q_EMIT valueChanged();
            } else {
                clear();
            }
        } else
        if(valid)
            setValue(val);
        else
            clear();
    }

    void setSingleStep(const CAmount& step)
    {
        singleStep = step;
    }

    QSize minimumSizeHint() const
    {
        if(cachedMinimumSizeHint.isEmpty())
        {
            ensurePolished();

            const QFontMetrics fm(fontMetrics());
            int h = lineEdit()->minimumSizeHint().height();
            int w = fm.width(BitcoinUnits::format(BitcoinUnits::BTC, BitcoinUnits::maxMoney(), false, BitcoinUnits::separatorAlways));
            w += 2; // cursor blinking space

            QStyleOptionSpinBox opt;
            initStyleOption(&opt);
            QSize hint(w, h);
            QSize extra(35, 6);
            opt.rect.setSize(hint + extra);
            extra += hint - style()->subControlRect(QStyle::CC_SpinBox, &opt,
                                                    QStyle::SC_SpinBoxEditField, this).size();
            // get closer to final result by repeating the calculation
            opt.rect.setSize(hint + extra);
            extra += hint - style()->subControlRect(QStyle::CC_SpinBox, &opt,
                                                    QStyle::SC_SpinBoxEditField, this).size();
            hint += extra;
            hint.setHeight(h);

            opt.rect = rect();

            cachedMinimumSizeHint = style()->sizeFromContents(QStyle::CT_SpinBox, &opt, hint, this)
                                    .expandedTo(QApplication::globalStrut());
        }
        return cachedMinimumSizeHint;
    }

private:
    CAsset current_asset;
    int currentUnit;
    CAmount singleStep;
    mutable QSize cachedMinimumSizeHint;

    /**
     * Parse a string into a number of base monetary units and
     * return validity.
     * @note Must return 0 if !valid.
     */
    CAmount parse(const QString &text, bool *valid_out=0) const
    {
        CAmount val = 0;
        bool valid = GUIUtil::parseAssetAmount(current_asset, text, currentUnit, &val);
        if(valid)
        {
            if (val < 0 || (val > BitcoinUnits::maxMoney() && current_asset == Params().GetConsensus().pegged_asset)) {
                valid = false;
            }
        }
        if(valid_out)
            *valid_out = valid;
        return valid ? val : 0;
    }

protected:
    bool event(QEvent *event)
    {
        if (event->type() == QEvent::KeyPress || event->type() == QEvent::KeyRelease)
        {
            QKeyEvent *keyEvent = static_cast<QKeyEvent *>(event);
            if (keyEvent->key() == Qt::Key_Comma)
            {
                // Translate a comma into a period
                QKeyEvent periodKeyEvent(event->type(), Qt::Key_Period, keyEvent->modifiers(), ".", keyEvent->isAutoRepeat(), keyEvent->count());
                return QAbstractSpinBox::event(&periodKeyEvent);
            }
        }
        return QAbstractSpinBox::event(event);
    }

    StepEnabled stepEnabled() const
    {
        if (isReadOnly()) // Disable steps when AmountSpinBox is read-only
            return StepNone;
        if (text().isEmpty()) // Allow step-up with empty field
            return StepUpEnabled;

        StepEnabled rv = 0;
        bool valid = false;
        const std::pair<CAsset, CAmount> val = value(&valid);
        if(valid)
        {
            if (val.second > 0) {
                rv |= StepDownEnabled;
            }
            if (val.second < BitcoinUnits::maxMoney() || val.first != Params().GetConsensus().pegged_asset) {
                rv |= StepUpEnabled;
            }
        }
        return rv;
    }

Q_SIGNALS:
    void valueChanged();
};

#include <qt/bitcoinamountfield.moc>

BitcoinAmountField::BitcoinAmountField(std::set<CAsset> allowed_assets, QWidget *parent) :
    QWidget(parent),
    m_allowed_assets(allowed_assets),
    amount(0)
{
    amount = new AmountSpinBox(this);
    amount->setLocale(QLocale::c());
    amount->installEventFilter(this);
    amount->setMaximumWidth(240);

    QHBoxLayout *layout = new QHBoxLayout(this);
    layout->addWidget(amount);
    unit = new QComboBox(this);
    m_allowed_assets = allowed_assets;
    for (const auto& asset : allowed_assets) {
        if (asset == Params().GetConsensus().pegged_asset) {
            // Special handling
            for (const auto& pegged_unit : BitcoinUnits::availableUnits()) {
                unit->addItem(BitcoinUnits::shortName(pegged_unit), int(pegged_unit));
            }
            continue;
        }
        unit->addItem(QString::fromStdString(gAssetsDir.GetIdentifier(asset)), QVariant::fromValue(asset));
    }
    layout->addWidget(unit);
    layout->addStretch(1);
    layout->setContentsMargins(0,0,0,0);

    setLayout(layout);

    setFocusPolicy(Qt::TabFocus);
    setFocusProxy(amount);

    // If one if the widgets changes, the combined content changes as well
    connect(amount, &AmountSpinBox::valueChanged, this, &BitcoinAmountField::valueChanged);
    connect(unit, static_cast<void (QComboBox::*)(int)>(&QComboBox::currentIndexChanged), this, &BitcoinAmountField::unitChanged);

    // Set default based on configuration
    unitChanged(unit->currentIndex());
}

BitcoinAmountField::BitcoinAmountField(QWidget *parent) :
    BitcoinAmountField(std::set<CAsset>({Params().GetConsensus().pegged_asset}), parent)
{
}

void BitcoinAmountField::clear()
{
    amount->clear();
    unit->setCurrentIndex(0);
}

void BitcoinAmountField::setEnabled(bool fEnabled)
{
    amount->setEnabled(fEnabled);
    unit->setEnabled(fEnabled);
}

bool BitcoinAmountField::validate()
{
    bool valid = false;
    fullValue(&valid);
    setValid(valid);
    return valid;
}

void BitcoinAmountField::setValid(bool valid)
{
    if (valid)
        amount->setStyleSheet("");
    else
        amount->setStyleSheet(STYLE_INVALID);
}

bool BitcoinAmountField::eventFilter(QObject *object, QEvent *event)
{
    if (event->type() == QEvent::FocusIn)
    {
        // Clear invalid flag on focus
        setValid(true);
    }
    return QWidget::eventFilter(object, event);
}

QWidget *BitcoinAmountField::setupTabChain(QWidget *prev)
{
    QWidget::setTabOrder(prev, amount);
    QWidget::setTabOrder(amount, unit);
    return unit;
}

std::pair<CAsset, CAmount> BitcoinAmountField::fullValue(bool *valid_out) const
{
    return amount->value(valid_out);
}

void BitcoinAmountField::setFullValue(const CAsset& asset, const CAmount& value)
{
    amount->setValue(asset, value);
    setDisplayUnit(asset);
}

CAmount BitcoinAmountField::value(bool *valid_out) const
{
    std::pair<CAsset, CAmount> val = amount->value(valid_out);
    assert(val.first == Params().GetConsensus().pegged_asset);
    return val.second;
}

void BitcoinAmountField::setValue(const CAmount& value)
{
    amount->setValue(Params().GetConsensus().pegged_asset, value);
    setDisplayUnit(amount->currentPeggedUnit());
}

void BitcoinAmountField::setReadOnly(bool fReadOnly)
{
    amount->setReadOnly(fReadOnly);
}

void BitcoinAmountField::unitChanged(int idx)
{
    // Use description tooltip for current unit for the combobox
    const QVariant& userdata = unit->itemData(idx, Qt::UserRole);
    if (userdata.type() == QVariant::UserType) {
        const CAsset asset = userdata.value<CAsset>();
        unit->setToolTip(tr("Custom asset (%1)").arg(QString::fromStdString(asset.GetHex())));

        amount->setDisplayUnit(asset);
    } else {
        // Determine new unit ID
        int newUnit = userdata.toInt();

        unit->setToolTip(BitcoinUnits::description(newUnit));

        amount->setDisplayUnit(newUnit);
    }
}

void BitcoinAmountField::setDisplayUnit(const CAsset& asset)
{
    if (asset == Params().GetConsensus().pegged_asset) {
        setDisplayUnit(amount->currentPeggedUnit());
        return;
    }
    // TODO: make sure it's an item
    unit->setCurrentIndex(unit->findData(QVariant::fromValue(asset), Qt::UserRole));
}

void BitcoinAmountField::setDisplayUnit(int newUnit)
{
    unit->setCurrentIndex(unit->findData(newUnit, Qt::UserRole));
}

void BitcoinAmountField::setSingleStep(const CAmount& step)
{
    amount->setSingleStep(step);
}
