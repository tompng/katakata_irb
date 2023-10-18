# frozen_string_literal: true

require 'ripper'
require 'test_helper'

KatakataIrb::Types.preload_in_thread.join

class TestKatakataIrb < Minitest::Test
  def test_analyze_does_not_raise_error
    verbose, $VERBOSE = $VERBOSE, nil
    original_output = KatakataIrb.log_output
    KatakataIrb::TypeAnalyzer::DigTarget.class_eval do
      alias_method :original_dig?, :dig?
      def dig?(node) = !!node
    end
    KatakataIrb.log_output = Object.new.tap do |output|
      def output.puts(*)
        raise 'Unexpected log output in test'
      end
    end

    # Should analyze whole code in this repository
    files = Dir.glob('lib/**/*.rb') + Dir.glob('test/**/*.rb')
    files.each do |file|
      result = KatakataIrb::Completor.analyze("(\n#{File.read(file)}\n).hoge") rescue nil
      assert result, "analyzing #{file}"
    end
  ensure
    $VERBOSE = verbose
    KatakataIrb.log_output = original_output
    KatakataIrb::TypeAnalyzer::DigTarget.class_eval do
      undef_method :dig?
      alias_method :dig?, :original_dig?
    end
  end

  def test_irb_completor_compatibility
    if IRB.const_defined? :RegexpCompletor # IRB::VERSION >= 1.8.2
      completion = IRB::RegexpCompletor.new.completion_candidates '', 'at_exi', '', bind: binding
      assert_equal ['at_exit'], completion
      KatakataIrb::Completor.prev_analyze_result = KatakataIrb::Completor.analyze 'a = 1.to_c; a.abs', binding
      document = IRB::RegexpCompletor.new.doc_namespace 'a=1.to_c; ', 'a.abs', '', bind: binding
      assert_equal 'Complex#abs', document
    elsif IRB.const_defined? :InputCompletor # IRB::VERSION <= 1.8.1
      completion = IRB::InputCompletor.retrieve_completion_data 'at_exi', bind: binding, doc_namespace: false
      assert_equal ['at_exit'], completion
      KatakataIrb::Completor.prev_analyze_result = KatakataIrb::Completor.analyze 'a = 1.to_c; a.abs', binding
      document = IRB::InputCompletor.retrieve_completion_data 'a.abs', bind: binding, doc_namespace: true
      assert_equal 'Complex#abs', document
    else
      raise
    end
  end

  def test_prism_node_names
    files = %w[type_analyzer.rb completor.rb]
    codes = files.map do |file|
      File.read File.join(File.dirname(__FILE__), '../lib/katakata_irb', file)
    end
    implemented_node_class_names = [
      *codes.join.scan(/evaluate_[a-z_]+/).grep(/_node$/).map { "Prism::#{_1[9..].split('_').map(&:capitalize).join}" },
      *codes.join.scan(/Prism::[A-Za-z]+Node/)
    ].uniq.sort
    ignore_class_names = ['Prism::BlockLocalVariableNode']
    all_node_class_names = Prism.constants.grep(/Node$/).map { "Prism::#{_1}" }.sort - ['Prism::Node'] - ignore_class_names
    assert_empty implemented_node_class_names - all_node_class_names
    assert_empty all_node_class_names - implemented_node_class_names
  end
end
