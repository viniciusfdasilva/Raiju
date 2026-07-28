#pragma once

#include "AbstractValue.h"

class BoolValue : public AbstractValue<bool, 2> {
public:
  void join(const BoolValue &other);
  void addConstant(const std::vector<bool> &vals) override;
};