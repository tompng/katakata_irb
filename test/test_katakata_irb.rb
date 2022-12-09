# frozen_string_literal: true
require 'katakata_irb/completor'
require 'test_helper'

class TestKatakataIrb < Minitest::Test
  def test_analyze_does_not_raise_error
    KatakataIrb::TypeSimulator::DigTarget.class_eval do
      def dig?(*) = true
    end
    KatakataIrb.define_singleton_method(:log_puts) {|*| raise }
    Dir.glob '**/*.rb' do |file|
      assert KatakataIrb::Completor.analyze(File.read(file) + '.hoge'), "analyzing #{file}"
    end
  end
end
