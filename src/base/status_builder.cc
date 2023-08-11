//
// Copyright 2023 Google LLC
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//

// Based on similar utilities in ZetaSQL, with small modifications:
// https://github.com/google/zetasql/blob/master/zetasql/base/status_builder.cc

#include "src/base/status_builder.h"

#include <iostream>
#include <unordered_map>

#include "absl/status/status.h"
#include "absl/strings/str_cat.h"
#include "absl/log/log.h"
#include "src/base/source_location.h"

namespace smt::base {

static void CopyStatusPayloads(const absl::Status& from, absl::Status* to) {
  from.ForEachPayload([to](absl::string_view type_url, absl::Cord payload) {
    to->SetPayload(type_url, payload);
  });
}

StatusBuilder& StatusBuilder::SetErrorCode(absl::StatusCode code) {
  absl::Status tmp = absl::Status(code, status_.message());
  CopyStatusPayloads(status_, &tmp);
  status_ = std::move(tmp);
  return *this;
}

StatusBuilder::Rep::Rep(const Rep& r)
    : logging_mode(r.logging_mode),
      log_severity(r.log_severity),
      verbose_level(r.verbose_level),
      stream(),
      should_log_stack_trace(r.should_log_stack_trace),
      message_join_style(r.message_join_style) {
  stream << r.stream.str();
}

absl::Status StatusBuilder::JoinMessageToStatus(absl::Status s,
                                                absl::string_view msg,
                                                MessageJoinStyle style) {
  if (msg.empty()) return s;

  std::string new_msg;
  if (s.message().empty()) {
    new_msg = std::string(msg);
  } else if (style == MessageJoinStyle::kAnnotate) {
    new_msg = absl::StrCat(s.message(), "; ", msg);
  } else if (style == MessageJoinStyle::kPrepend) {
    new_msg = absl::StrCat(msg, s.message());
  } else {  // kAppend
    new_msg = absl::StrCat(s.message(), msg);
  }
  absl::Status tmp(s.code(), new_msg);
  CopyStatusPayloads(s, &tmp);
  return tmp;
}

void StatusBuilder::ConditionallyLog(const absl::Status& result) const {
  if (rep_->logging_mode == Rep::LoggingMode::kDisabled) return;

  LOG(LEVEL(rep_->log_severity))
          .AtLocation(location_.file_name(), location_.line())
      << result;
}

absl::Status StatusBuilder::CreateStatusAndConditionallyLog() && {
  absl::Status result = JoinMessageToStatus(
      std::move(status_), rep_->stream.str(), rep_->message_join_style);
  ConditionallyLog(result);

  // We consumed the status above, we set it to some error just to prevent
  // people relying on it become OK or something.
  status_ = absl::UnknownError("");
  rep_ = nullptr;
  return result;
}

StatusBuilder AbortedErrorBuilder(smt::base::SourceLocation location) {
  return StatusBuilder(absl::StatusCode::kAborted, location);
}

StatusBuilder AlreadyExistsErrorBuilder(smt::base::SourceLocation location) {
  return StatusBuilder(absl::StatusCode::kAlreadyExists, location);
}

StatusBuilder CancelledErrorBuilder(smt::base::SourceLocation location) {
  return StatusBuilder(absl::StatusCode::kCancelled, location);
}

StatusBuilder DataLossErrorBuilder(smt::base::SourceLocation location) {
  return StatusBuilder(absl::StatusCode::kDataLoss, location);
}

StatusBuilder DeadlineExceededErrorBuilder(
    smt::base::SourceLocation location) {
  return StatusBuilder(absl::StatusCode::kDeadlineExceeded, location);
}

StatusBuilder FailedPreconditionErrorBuilder(
    smt::base::SourceLocation location) {
  return StatusBuilder(absl::StatusCode::kFailedPrecondition, location);
}

StatusBuilder InternalErrorBuilder(smt::base::SourceLocation location) {
  return StatusBuilder(absl::StatusCode::kInternal, location);
}

StatusBuilder InvalidArgumentErrorBuilder(
    smt::base::SourceLocation location) {
  return StatusBuilder(absl::StatusCode::kInvalidArgument, location);
}

StatusBuilder NotFoundErrorBuilder(smt::base::SourceLocation location) {
  return StatusBuilder(absl::StatusCode::kNotFound, location);
}

StatusBuilder OutOfRangeErrorBuilder(smt::base::SourceLocation location) {
  return StatusBuilder(absl::StatusCode::kOutOfRange, location);
}

StatusBuilder PermissionDeniedErrorBuilder(
    smt::base::SourceLocation location) {
  return StatusBuilder(absl::StatusCode::kPermissionDenied, location);
}

StatusBuilder UnauthenticatedErrorBuilder(
    smt::base::SourceLocation location) {
  return StatusBuilder(absl::StatusCode::kUnauthenticated, location);
}

StatusBuilder ResourceExhaustedErrorBuilder(
    smt::base::SourceLocation location) {
  return StatusBuilder(absl::StatusCode::kResourceExhausted, location);
}

StatusBuilder UnavailableErrorBuilder(smt::base::SourceLocation location) {
  return StatusBuilder(absl::StatusCode::kUnavailable, location);
}

StatusBuilder UnimplementedErrorBuilder(smt::base::SourceLocation location) {
  return StatusBuilder(absl::StatusCode::kUnimplemented, location);
}

StatusBuilder UnknownErrorBuilder(smt::base::SourceLocation location) {
  return StatusBuilder(absl::StatusCode::kUnknown, location);
}

}  // namespace smt::base
