# frozen_string_literal: true
require "simplecov"
SimpleCov.start

$LOAD_PATH.unshift File.expand_path("../lib", __dir__)
require "katakata_irb"
require "minitest/autorun"

KatakataIrb.log_output = STDOUT