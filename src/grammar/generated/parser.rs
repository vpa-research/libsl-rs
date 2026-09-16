// Generated from ./LibSLParser.g4 by ANTLR 4.13.2
#![allow(dead_code)]
#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(nonstandard_style)]
#![allow(unused_imports)]
#![allow(unused_mut)]
#![allow(unused_braces)]
use antlr_rust::PredictionContextCache;
use antlr_rust::parser::{Parser, BaseParser, ParserRecog, ParserNodeType};
use antlr_rust::token_stream::TokenStream;
use antlr_rust::TokenSource;
use antlr_rust::parser_atn_simulator::ParserATNSimulator;
use antlr_rust::errors::*;
use antlr_rust::rule_context::{BaseRuleContext, CustomRuleContext, RuleContext};
use antlr_rust::recognizer::{Recognizer,Actions};
use antlr_rust::atn_deserializer::ATNDeserializer;
use antlr_rust::dfa::DFA;
use antlr_rust::atn::{ATN, INVALID_ALT};
use antlr_rust::error_strategy::{ErrorStrategy, DefaultErrorStrategy};
use antlr_rust::parser_rule_context::{BaseParserRuleContext, ParserRuleContext,cast,cast_mut};
use antlr_rust::tree::*;
use antlr_rust::token::{TOKEN_EOF,OwningToken,Token};
use antlr_rust::int_stream::EOF;
use antlr_rust::vocabulary::{Vocabulary,VocabularyImpl};
use antlr_rust::token_factory::{CommonTokenFactory,TokenFactory, TokenAware};
use super::libslparserlistener::*;
use antlr_rust::{TidAble,TidExt};

use std::marker::PhantomData;
use std::sync::{Arc, LazyLock};
use std::rc::Rc;
use std::convert::TryFrom;
use std::cell::RefCell;
use std::ops::{DerefMut, Deref};
use std::borrow::{Borrow,BorrowMut};
use std::any::{Any,TypeId};

		pub const SEMICOLON:isize=1; 
		pub const EQ:isize=2; 
		pub const EQ_EQ:isize=3; 
		pub const L_BRACE:isize=4; 
		pub const R_BRACE:isize=5; 
		pub const L_PAREN:isize=6; 
		pub const R_PAREN:isize=7; 
		pub const L_BRACKET:isize=8; 
		pub const R_BRACKET:isize=9; 
		pub const DOT:isize=10; 
		pub const COLON:isize=11; 
		pub const COMMA:isize=12; 
		pub const ARROW:isize=13; 
		pub const L_ANGLE:isize=14; 
		pub const R_ANGLE:isize=15; 
		pub const ASTERISK:isize=16; 
		pub const SLASH:isize=17; 
		pub const PERCENT:isize=18; 
		pub const PLUS:isize=19; 
		pub const MINUS:isize=20; 
		pub const PLUS_EQ:isize=21; 
		pub const MINUS_EQ:isize=22; 
		pub const ASTERISK_EQ:isize=23; 
		pub const SLASH_EQ:isize=24; 
		pub const PERCENT_EQ:isize=25; 
		pub const BANG:isize=26; 
		pub const BANG_EQ:isize=27; 
		pub const L_ANGLE_EQ:isize=28; 
		pub const R_ANGLE_EQ:isize=29; 
		pub const AMP:isize=30; 
		pub const AMP_AMP:isize=31; 
		pub const PIPE:isize=32; 
		pub const PIPE_PIPE:isize=33; 
		pub const CARET:isize=34; 
		pub const TILDE:isize=35; 
		pub const AMP_EQ:isize=36; 
		pub const PIPE_EQ:isize=37; 
		pub const CARET_EQ:isize=38; 
		pub const R_ANGLE_R_ANGLE_EQ:isize=39; 
		pub const L_ANGLE_L_ANGLE_EQ:isize=40; 
		pub const QUOTE:isize=41; 
		pub const BACKTICK:isize=42; 
		pub const IMPORT:isize=43; 
		pub const INCLUDE:isize=44; 
		pub const LIBSL:isize=45; 
		pub const LIBRARY:isize=46; 
		pub const VERSION:isize=47; 
		pub const LANGUAGE:isize=48; 
		pub const URL:isize=49; 
		pub const TYPEALIAS:isize=50; 
		pub const TYPE:isize=51; 
		pub const TYPES:isize=52; 
		pub const ENUM:isize=53; 
		pub const ANNOTATION:isize=54; 
		pub const AUTOMATON:isize=55; 
		pub const CONCEPT:isize=56; 
		pub const VAR:isize=57; 
		pub const VAL:isize=58; 
		pub const INITSTATE:isize=59; 
		pub const STATE:isize=60; 
		pub const FINISHSTATE:isize=61; 
		pub const SHIFT:isize=62; 
		pub const NEW:isize=63; 
		pub const FUN:isize=64; 
		pub const CONSTRUCTOR:isize=65; 
		pub const DESTRUCTOR:isize=66; 
		pub const PROC:isize=67; 
		pub const PRED:isize=68; 
		pub const ACTION:isize=69; 
		pub const REQUIRES:isize=70; 
		pub const ENSURES:isize=71; 
		pub const ASSIGNS:isize=72; 
		pub const TRUE:isize=73; 
		pub const FALSE:isize=74; 
		pub const DEFINE:isize=75; 
		pub const IF:isize=76; 
		pub const ELSE:isize=77; 
		pub const BY:isize=78; 
		pub const IS:isize=79; 
		pub const AS:isize=80; 
		pub const NULL:isize=81; 
		pub const IN:isize=82; 
		pub const OUT:isize=83; 
		pub const WHERE:isize=84; 
		pub const FOR:isize=85; 
		pub const IMPLEMENTS:isize=86; 
		pub const STATIC:isize=87; 
		pub const PURE:isize=88; 
		pub const HAS:isize=89; 
		pub const QUESTION:isize=90; 
		pub const CANCEL:isize=91; 
		pub const IntegerLit:isize=92; 
		pub const AT:isize=93; 
		pub const FloatLit:isize=94; 
		pub const Identifier:isize=95; 
		pub const StringLit:isize=96; 
		pub const CharacterLit:isize=97; 
		pub const Digit:isize=98; 
		pub const Ignored:isize=99; 
		pub const PathIgnored:isize=100; 
		pub const BarePath:isize=101;
	pub const RULE_file:usize = 0; 
	pub const RULE_header:usize = 1; 
	pub const RULE_globalDecl:usize = 2; 
	pub const RULE_importDecl:usize = 3; 
	pub const RULE_includeDecl:usize = 4; 
	pub const RULE_path:usize = 5; 
	pub const RULE_semanticTypeSectionDecl:usize = 6; 
	pub const RULE_semanticTypeDecl:usize = 7; 
	pub const RULE_semanticTypeDef:usize = 8; 
	pub const RULE_enumSemanticTypeValue:usize = 9; 
	pub const RULE_typeAliasDecl:usize = 10; 
	pub const RULE_structDecl:usize = 11; 
	pub const RULE_structTargetType:usize = 12; 
	pub const RULE_structDefDecl:usize = 13; 
	pub const RULE_enumDecl:usize = 14; 
	pub const RULE_enumDeclVariant:usize = 15; 
	pub const RULE_signedIntLit:usize = 16; 
	pub const RULE_sign:usize = 17; 
	pub const RULE_annotationDecl:usize = 18; 
	pub const RULE_annotationParamList:usize = 19; 
	pub const RULE_annotationParam:usize = 20; 
	pub const RULE_actionDecl:usize = 21; 
	pub const RULE_actionParamList:usize = 22; 
	pub const RULE_actionParam:usize = 23; 
	pub const RULE_automatonDecl:usize = 24; 
	pub const RULE_constructorVariableList:usize = 25; 
	pub const RULE_constructorVariable:usize = 26; 
	pub const RULE_implementedConcepts:usize = 27; 
	pub const RULE_automatonDefDecl:usize = 28; 
	pub const RULE_functionDecl:usize = 29; 
	pub const RULE_functionModifier:usize = 30; 
	pub const RULE_methodSpec:usize = 31; 
	pub const RULE_functionDef:usize = 32; 
	pub const RULE_predDecl:usize = 33; 
	pub const RULE_variableDecl:usize = 34; 
	pub const RULE_variableKind:usize = 35; 
	pub const RULE_stateDecl:usize = 36; 
	pub const RULE_stateKind:usize = 37; 
	pub const RULE_identList:usize = 38; 
	pub const RULE_shiftDecl:usize = 39; 
	pub const RULE_shiftSourceState:usize = 40; 
	pub const RULE_shiftBy:usize = 41; 
	pub const RULE_functionSignatureList:usize = 42; 
	pub const RULE_functionSignature:usize = 43; 
	pub const RULE_constructorDecl:usize = 44; 
	pub const RULE_destructorDecl:usize = 45; 
	pub const RULE_procDecl:usize = 46; 
	pub const RULE_procModifier:usize = 47; 
	pub const RULE_functionParamList:usize = 48; 
	pub const RULE_functionParam:usize = 49; 
	pub const RULE_functionBody:usize = 50; 
	pub const RULE_contract:usize = 51; 
	pub const RULE_requiresContract:usize = 52; 
	pub const RULE_ensuresContract:usize = 53; 
	pub const RULE_assignsContract:usize = 54; 
	pub const RULE_contractPredicate:usize = 55; 
	pub const RULE_exprPredicate:usize = 56; 
	pub const RULE_predicate:usize = 57; 
	pub const RULE_blockPredicate:usize = 58; 
	pub const RULE_ifPredicate:usize = 59; 
	pub const RULE_annotation:usize = 60; 
	pub const RULE_annotationArgList:usize = 61; 
	pub const RULE_annotationArg:usize = 62; 
	pub const RULE_qualifiedTypeName:usize = 63; 
	pub const RULE_fullName:usize = 64; 
	pub const RULE_whereClause:usize = 65; 
	pub const RULE_typeConstraint:usize = 66; 
	pub const RULE_generics:usize = 67; 
	pub const RULE_genericList:usize = 68; 
	pub const RULE_generic:usize = 69; 
	pub const RULE_varianceSpec:usize = 70; 
	pub const RULE_typeExprList:usize = 71; 
	pub const RULE_atomicTypeExpr:usize = 72; 
	pub const RULE_typeExpr:usize = 73; 
	pub const RULE_nameTypeExpr:usize = 74; 
	pub const RULE_pointerTypeExpr:usize = 75; 
	pub const RULE_typeArgSpec:usize = 76; 
	pub const RULE_typeArgList:usize = 77; 
	pub const RULE_typeArg:usize = 78; 
	pub const RULE_block:usize = 79; 
	pub const RULE_stmt:usize = 80; 
	pub const RULE_ifStmt:usize = 81; 
	pub const RULE_assignStmt:usize = 82; 
	pub const RULE_assignee:usize = 83; 
	pub const RULE_cancelStmt:usize = 84; 
	pub const RULE_assignOp:usize = 85; 
	pub const RULE_exprList:usize = 86; 
	pub const RULE_atomicExpr:usize = 87; 
	pub const RULE_signedNumLit:usize = 88; 
	pub const RULE_expr:usize = 89; 
	pub const RULE_unOp:usize = 90; 
	pub const RULE_mulBinOp:usize = 91; 
	pub const RULE_addBinOp:usize = 92; 
	pub const RULE_bitShiftOp:usize = 93; 
	pub const RULE_relOp:usize = 94; 
	pub const RULE_primitiveLit:usize = 95; 
	pub const RULE_arrayLitExpr:usize = 96; 
	pub const RULE_setLitExpr:usize = 97; 
	pub const RULE_actionCallExpr:usize = 98; 
	pub const RULE_instantiationExpr:usize = 99; 
	pub const RULE_constructorArgList:usize = 100; 
	pub const RULE_constructorArg:usize = 101; 
	pub const RULE_ident:usize = 102;
	pub const ruleNames: [&'static str; 103] =  [
		"file", "header", "globalDecl", "importDecl", "includeDecl", "path", "semanticTypeSectionDecl", 
		"semanticTypeDecl", "semanticTypeDef", "enumSemanticTypeValue", "typeAliasDecl", 
		"structDecl", "structTargetType", "structDefDecl", "enumDecl", "enumDeclVariant", 
		"signedIntLit", "sign", "annotationDecl", "annotationParamList", "annotationParam", 
		"actionDecl", "actionParamList", "actionParam", "automatonDecl", "constructorVariableList", 
		"constructorVariable", "implementedConcepts", "automatonDefDecl", "functionDecl", 
		"functionModifier", "methodSpec", "functionDef", "predDecl", "variableDecl", 
		"variableKind", "stateDecl", "stateKind", "identList", "shiftDecl", "shiftSourceState", 
		"shiftBy", "functionSignatureList", "functionSignature", "constructorDecl", 
		"destructorDecl", "procDecl", "procModifier", "functionParamList", "functionParam", 
		"functionBody", "contract", "requiresContract", "ensuresContract", "assignsContract", 
		"contractPredicate", "exprPredicate", "predicate", "blockPredicate", "ifPredicate", 
		"annotation", "annotationArgList", "annotationArg", "qualifiedTypeName", 
		"fullName", "whereClause", "typeConstraint", "generics", "genericList", 
		"generic", "varianceSpec", "typeExprList", "atomicTypeExpr", "typeExpr", 
		"nameTypeExpr", "pointerTypeExpr", "typeArgSpec", "typeArgList", "typeArg", 
		"block", "stmt", "ifStmt", "assignStmt", "assignee", "cancelStmt", "assignOp", 
		"exprList", "atomicExpr", "signedNumLit", "expr", "unOp", "mulBinOp", 
		"addBinOp", "bitShiftOp", "relOp", "primitiveLit", "arrayLitExpr", "setLitExpr", 
		"actionCallExpr", "instantiationExpr", "constructorArgList", "constructorArg", 
		"ident"
	];


	pub const _LITERAL_NAMES: [Option<&'static str>;94] = [
		None, None, Some("'='"), Some("'=='"), Some("'{'"), Some("'}'"), Some("'('"), 
		Some("')'"), Some("'['"), Some("']'"), Some("'.'"), Some("':'"), Some("','"), 
		Some("'->'"), Some("'<'"), Some("'>'"), Some("'*'"), Some("'/'"), Some("'%'"), 
		Some("'+'"), Some("'-'"), Some("'+='"), Some("'-='"), Some("'*='"), Some("'/='"), 
		Some("'%='"), Some("'!'"), Some("'!='"), Some("'<='"), Some("'>='"), Some("'&'"), 
		Some("'&&'"), Some("'|'"), Some("'||'"), Some("'^'"), Some("'~'"), Some("'&='"), 
		Some("'|='"), Some("'^='"), Some("'>>='"), Some("'<<='"), Some("'''"), 
		Some("'`'"), Some("'import'"), Some("'include'"), Some("'libsl'"), Some("'library'"), 
		Some("'version'"), Some("'language'"), Some("'url'"), Some("'typealias'"), 
		Some("'type'"), Some("'types'"), Some("'enum'"), Some("'annotation'"), 
		Some("'automaton'"), Some("'concept'"), Some("'var'"), Some("'val'"), 
		Some("'initstate'"), Some("'state'"), Some("'finishstate'"), Some("'shift'"), 
		Some("'new'"), Some("'fun'"), Some("'constructor'"), Some("'destructor'"), 
		Some("'proc'"), Some("'pred'"), Some("'action'"), Some("'requires'"), 
		Some("'ensures'"), Some("'assigns'"), Some("'true'"), Some("'false'"), 
		Some("'define'"), Some("'if'"), Some("'else'"), Some("'by'"), Some("'is'"), 
		Some("'as'"), Some("'null'"), Some("'in'"), Some("'out'"), Some("'where'"), 
		Some("'for'"), Some("'implements'"), Some("'static'"), Some("'pure'"), 
		Some("'has'"), Some("'?'"), Some("'cancel'"), None, Some("'@'")
	];
	pub const _SYMBOLIC_NAMES: [Option<&'static str>;102]  = [
		None, Some("SEMICOLON"), Some("EQ"), Some("EQ_EQ"), Some("L_BRACE"), Some("R_BRACE"), 
		Some("L_PAREN"), Some("R_PAREN"), Some("L_BRACKET"), Some("R_BRACKET"), 
		Some("DOT"), Some("COLON"), Some("COMMA"), Some("ARROW"), Some("L_ANGLE"), 
		Some("R_ANGLE"), Some("ASTERISK"), Some("SLASH"), Some("PERCENT"), Some("PLUS"), 
		Some("MINUS"), Some("PLUS_EQ"), Some("MINUS_EQ"), Some("ASTERISK_EQ"), 
		Some("SLASH_EQ"), Some("PERCENT_EQ"), Some("BANG"), Some("BANG_EQ"), Some("L_ANGLE_EQ"), 
		Some("R_ANGLE_EQ"), Some("AMP"), Some("AMP_AMP"), Some("PIPE"), Some("PIPE_PIPE"), 
		Some("CARET"), Some("TILDE"), Some("AMP_EQ"), Some("PIPE_EQ"), Some("CARET_EQ"), 
		Some("R_ANGLE_R_ANGLE_EQ"), Some("L_ANGLE_L_ANGLE_EQ"), Some("QUOTE"), 
		Some("BACKTICK"), Some("IMPORT"), Some("INCLUDE"), Some("LIBSL"), Some("LIBRARY"), 
		Some("VERSION"), Some("LANGUAGE"), Some("URL"), Some("TYPEALIAS"), Some("TYPE"), 
		Some("TYPES"), Some("ENUM"), Some("ANNOTATION"), Some("AUTOMATON"), Some("CONCEPT"), 
		Some("VAR"), Some("VAL"), Some("INITSTATE"), Some("STATE"), Some("FINISHSTATE"), 
		Some("SHIFT"), Some("NEW"), Some("FUN"), Some("CONSTRUCTOR"), Some("DESTRUCTOR"), 
		Some("PROC"), Some("PRED"), Some("ACTION"), Some("REQUIRES"), Some("ENSURES"), 
		Some("ASSIGNS"), Some("TRUE"), Some("FALSE"), Some("DEFINE"), Some("IF"), 
		Some("ELSE"), Some("BY"), Some("IS"), Some("AS"), Some("NULL"), Some("IN"), 
		Some("OUT"), Some("WHERE"), Some("FOR"), Some("IMPLEMENTS"), Some("STATIC"), 
		Some("PURE"), Some("HAS"), Some("QUESTION"), Some("CANCEL"), Some("IntegerLit"), 
		Some("AT"), Some("FloatLit"), Some("Identifier"), Some("StringLit"), Some("CharacterLit"), 
		Some("Digit"), Some("Ignored"), Some("PathIgnored"), Some("BarePath")
	];

	static _shared_context_cache: LazyLock<Arc<PredictionContextCache>> = LazyLock::new(||
	    Arc::new(PredictionContextCache::new())
	);
	static VOCABULARY: LazyLock<Box<dyn Vocabulary + Send>> = LazyLock::new(||
	    Box::new(VocabularyImpl::new(_LITERAL_NAMES.iter(), _SYMBOLIC_NAMES.iter(), None))
	);


type BaseParserType<'input, I> =
	BaseParser<'input,LibSLParserExt<'input>, I, LibSLParserContextType , dyn LibSLParserListener<'input> + 'input >;

type TokenType<'input> = <LocalTokenFactory<'input> as TokenFactory<'input>>::Tok;
pub type LocalTokenFactory<'input> = CommonTokenFactory;

pub type LibSLParserTreeWalker<'input,'a> =
	ParseTreeWalker<'input, 'a, LibSLParserContextType , dyn LibSLParserListener<'input> + 'a>;

/// Parser for LibSLParser grammar
pub struct LibSLParser<'input,I,H>
where
    I: TokenStream<'input, TF = LocalTokenFactory<'input> > + TidAble<'input>,
    H: ErrorStrategy<'input,BaseParserType<'input,I>>
{
	base:BaseParserType<'input,I>,
	interpreter:Arc<ParserATNSimulator>,
	_shared_context_cache: Box<PredictionContextCache>,
    pub err_handler: H,
}

impl<'input, I, H> LibSLParser<'input, I, H>
where
    I: TokenStream<'input, TF = LocalTokenFactory<'input> > + TidAble<'input>,
    H: ErrorStrategy<'input,BaseParserType<'input,I>>
{
	pub fn get_serialized_atn() -> &'static [isize] { _serializedATN }

    pub fn set_error_strategy(&mut self, strategy: H) {
        self.err_handler = strategy
    }

    pub fn with_strategy(input: I, strategy: H) -> Self {
		antlr_rust::recognizer::check_version("0","4");
		let interpreter = Arc::new(ParserATNSimulator::new(
			_ATN.clone(),
			_decision_to_DFA.clone(),
			_shared_context_cache.clone(),
		));
		Self {
			base: BaseParser::new_base_parser(
				input,
				Arc::clone(&interpreter),
				LibSLParserExt{
					_pd: Default::default(),
				}
			),
			interpreter,
            _shared_context_cache: Box::new(PredictionContextCache::new()),
            err_handler: strategy,
        }
    }

}

type DynStrategy<'input,I> = Box<dyn ErrorStrategy<'input,BaseParserType<'input,I>> + 'input>;

impl<'input, I> LibSLParser<'input, I, DynStrategy<'input,I>>
where
    I: TokenStream<'input, TF = LocalTokenFactory<'input> > + TidAble<'input>,
{
    pub fn with_dyn_strategy(input: I) -> Self{
    	Self::with_strategy(input,Box::new(DefaultErrorStrategy::new()))
    }
}

impl<'input, I> LibSLParser<'input, I, DefaultErrorStrategy<'input,LibSLParserContextType>>
where
    I: TokenStream<'input, TF = LocalTokenFactory<'input> > + TidAble<'input>,
{
    pub fn new(input: I) -> Self{
    	Self::with_strategy(input,DefaultErrorStrategy::new())
    }
}

/// Trait for monomorphized trait object that corresponds to the nodes of parse tree generated for LibSLParser
pub trait LibSLParserContext<'input>:
	for<'x> Listenable<dyn LibSLParserListener<'input> + 'x > + 
	ParserRuleContext<'input, TF=LocalTokenFactory<'input>, Ctx=LibSLParserContextType>
{}

antlr_rust::coerce_from!{ 'input : LibSLParserContext<'input> }

impl<'input> LibSLParserContext<'input> for TerminalNode<'input,LibSLParserContextType> {}
impl<'input> LibSLParserContext<'input> for ErrorNode<'input,LibSLParserContextType> {}

antlr_rust::tid! { impl<'input> TidAble<'input> for dyn LibSLParserContext<'input> + 'input }

antlr_rust::tid! { impl<'input> TidAble<'input> for dyn LibSLParserListener<'input> + 'input }

pub struct LibSLParserContextType;
antlr_rust::tid!{LibSLParserContextType}

impl<'input> ParserNodeType<'input> for LibSLParserContextType{
	type TF = LocalTokenFactory<'input>;
	type Type = dyn LibSLParserContext<'input> + 'input;
}

impl<'input, I, H> Deref for LibSLParser<'input, I, H>
where
    I: TokenStream<'input, TF = LocalTokenFactory<'input> > + TidAble<'input>,
    H: ErrorStrategy<'input,BaseParserType<'input,I>>
{
    type Target = BaseParserType<'input,I>;

    fn deref(&self) -> &Self::Target {
        &self.base
    }
}

impl<'input, I, H> DerefMut for LibSLParser<'input, I, H>
where
    I: TokenStream<'input, TF = LocalTokenFactory<'input> > + TidAble<'input>,
    H: ErrorStrategy<'input,BaseParserType<'input,I>>
{
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.base
    }
}

pub struct LibSLParserExt<'input>{
	_pd: PhantomData<&'input str>,
}

impl<'input> LibSLParserExt<'input>{
}
antlr_rust::tid! { LibSLParserExt<'a> }

impl<'input> TokenAware<'input> for LibSLParserExt<'input>{
	type TF = LocalTokenFactory<'input>;
}

impl<'input,I: TokenStream<'input, TF = LocalTokenFactory<'input> > + TidAble<'input>> ParserRecog<'input, BaseParserType<'input,I>> for LibSLParserExt<'input>{}

impl<'input,I: TokenStream<'input, TF = LocalTokenFactory<'input> > + TidAble<'input>> Actions<'input, BaseParserType<'input,I>> for LibSLParserExt<'input>{
	fn get_grammar_file_name(&self) -> & str{ "LibSLParser.g4"}

   	fn get_rule_names(&self) -> &[& str] {&ruleNames}

   	fn get_vocabulary(&self) -> &dyn Vocabulary { &**VOCABULARY }
	fn sempred(_localctx: Option<&(dyn LibSLParserContext<'input> + 'input)>, rule_index: isize, pred_index: isize,
			   recog:&mut BaseParserType<'input,I>
	)->bool{
		match rule_index {
					73 => LibSLParser::<'input,I,_>::typeExpr_sempred(_localctx.and_then(|x|x.downcast_ref()), pred_index, recog),
					89 => LibSLParser::<'input,I,_>::expr_sempred(_localctx.and_then(|x|x.downcast_ref()), pred_index, recog),
			_ => true
		}
	}
}

impl<'input, I> LibSLParser<'input, I, DefaultErrorStrategy<'input,LibSLParserContextType>>
where
    I: TokenStream<'input, TF = LocalTokenFactory<'input> > + TidAble<'input>,
{
	fn typeExpr_sempred(_localctx: Option<&TypeExprContext<'input>>, pred_index:isize,
						recog:&mut <Self as Deref>::Target
		) -> bool {
		match pred_index {
				0=>{
					recog.precpred(None, 2)
				}
				1=>{
					recog.precpred(None, 1)
				}
			_ => true
		}
	}
	fn expr_sempred(_localctx: Option<&ExprContext<'input>>, pred_index:isize,
						recog:&mut <Self as Deref>::Target
		) -> bool {
		match pred_index {
				2=>{
					recog.precpred(None, 9)
				}
				3=>{
					recog.precpred(None, 8)
				}
				4=>{
					recog.precpred(None, 7)
				}
				5=>{
					recog.precpred(None, 6)
				}
				6=>{
					recog.precpred(None, 5)
				}
				7=>{
					recog.precpred(None, 4)
				}
				8=>{
					recog.precpred(None, 3)
				}
				9=>{
					recog.precpred(None, 2)
				}
				10=>{
					recog.precpred(None, 1)
				}
				11=>{
					recog.precpred(None, 18)
				}
				12=>{
					recog.precpred(None, 17)
				}
				13=>{
					recog.precpred(None, 16)
				}
				14=>{
					recog.precpred(None, 15)
				}
				15=>{
					recog.precpred(None, 14)
				}
				16=>{
					recog.precpred(None, 12)
				}
				17=>{
					recog.precpred(None, 11)
				}
				18=>{
					recog.precpred(None, 10)
				}
			_ => true
		}
	}
}
//------------------- file ----------------
pub type FileContextAll<'input> = FileContext<'input>;


pub type FileContext<'input> = BaseParserRuleContext<'input,FileContextExt<'input>>;

#[derive(Clone)]
pub struct FileContextExt<'input>{
	pub globalDecl: Option<Rc<GlobalDeclContextAll<'input>>>,
	pub decls:Vec<Rc<GlobalDeclContextAll<'input>>>,
ph:PhantomData<&'input str>
}

impl<'input> LibSLParserContext<'input> for FileContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for FileContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_file(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_file(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for FileContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_file }
	//fn type_rule_index() -> usize where Self: Sized { RULE_file }
}
antlr_rust::tid!{FileContextExt<'a>}

impl<'input> FileContextExt<'input>{
	fn new(parent: Option<Rc<dyn LibSLParserContext<'input> + 'input > >, invoking_state: isize) -> Rc<FileContextAll<'input>> {
		Rc::new(
			BaseParserRuleContext::new_parser_ctx(parent, invoking_state,FileContextExt{
				globalDecl: None, 
				decls: Vec::new(), 
				ph:PhantomData
			}),
		)
	}
}

pub trait FileContextAttrs<'input>: LibSLParserContext<'input> + BorrowMut<FileContextExt<'input>>{

/// Retrieves first TerminalNode corresponding to token EOF
/// Returns `None` if there is no child corresponding to token EOF
fn EOF(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(EOF, 0)
}
fn header(&self) -> Option<Rc<HeaderContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}
fn globalDecl_all(&self) ->  Vec<Rc<GlobalDeclContextAll<'input>>> where Self:Sized{
	self.children_of_type()
}
fn globalDecl(&self, i: usize) -> Option<Rc<GlobalDeclContextAll<'input>>> where Self:Sized{
	self.child_of_type(i)
}

}

impl<'input> FileContextAttrs<'input> for FileContext<'input>{}

impl<'input, I, H> LibSLParser<'input, I, H>
where
    I: TokenStream<'input, TF = LocalTokenFactory<'input> > + TidAble<'input>,
    H: ErrorStrategy<'input,BaseParserType<'input,I>>
{
	pub fn file(&mut self,)
	-> Result<Rc<FileContextAll<'input>>,ANTLRError> {
		let mut recog = self;
		let _parentctx = recog.ctx.take();
		let mut _localctx = FileContextExt::new(_parentctx.clone(), recog.base.get_state());
        recog.base.enter_rule(_localctx.clone(), 0, RULE_file);
        let mut _localctx: Rc<FileContextAll> = _localctx;
		let mut _la: isize = -1;
		let result: Result<(), ANTLRError> = (|| {

			//recog.base.enter_outer_alt(_localctx.clone(), 1);
			recog.base.enter_outer_alt(None, 1);
			{
			recog.base.set_state(207);
			recog.err_handler.sync(&mut recog.base)?;
			_la = recog.base.input.la(1);
			if _la==LIBSL {
				{
				/*InvokeRule header*/
				recog.base.set_state(206);
				recog.header()?;

				}
			}

			recog.base.set_state(212);
			recog.err_handler.sync(&mut recog.base)?;
			_la = recog.base.input.la(1);
			while ((((_la - 43)) & !0x3f) == 0 && ((1usize << (_la - 43)) & 52486019) != 0) || ((((_la - 75)) & !0x3f) == 0 && ((1usize << (_la - 75)) & 274433) != 0) {
				{
				{
				/*InvokeRule globalDecl*/
				recog.base.set_state(209);
				let tmp = recog.globalDecl()?;
				 cast_mut::<_,FileContext >(&mut _localctx).globalDecl = Some(tmp.clone());
				  

				let temp =  cast_mut::<_,FileContext >(&mut _localctx).globalDecl.clone().unwrap()
				 ;
				 cast_mut::<_,FileContext >(&mut _localctx).decls.push(temp);
				  
				}
				}
				recog.base.set_state(214);
				recog.err_handler.sync(&mut recog.base)?;
				_la = recog.base.input.la(1);
			}
			recog.base.set_state(215);
			recog.base.match_token(EOF,&mut recog.err_handler)?;

			}
			Ok(())
		})();
		match result {
		Ok(_)=>{},
        Err(e @ ANTLRError::FallThrough(_)) => return Err(e),
		Err(ref re) => {
				//_localctx.exception = re;
				recog.err_handler.report_error(&mut recog.base, re);
				recog.err_handler.recover(&mut recog.base, re)?;
			}
		}
		recog.base.exit_rule();

		Ok(_localctx)
	}
}
//------------------- header ----------------
pub type HeaderContextAll<'input> = HeaderContext<'input>;


pub type HeaderContext<'input> = BaseParserRuleContext<'input,HeaderContextExt<'input>>;

#[derive(Clone)]
pub struct HeaderContextExt<'input>{
	pub libslVersion: Option<TokenType<'input>>,
	pub libraryName: Option<Rc<IdentContextAll<'input>>>,
	pub version: Option<TokenType<'input>>,
	pub language: Option<TokenType<'input>>,
	pub url: Option<TokenType<'input>>,
ph:PhantomData<&'input str>
}

impl<'input> LibSLParserContext<'input> for HeaderContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for HeaderContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_header(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_header(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for HeaderContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_header }
	//fn type_rule_index() -> usize where Self: Sized { RULE_header }
}
antlr_rust::tid!{HeaderContextExt<'a>}

impl<'input> HeaderContextExt<'input>{
	fn new(parent: Option<Rc<dyn LibSLParserContext<'input> + 'input > >, invoking_state: isize) -> Rc<HeaderContextAll<'input>> {
		Rc::new(
			BaseParserRuleContext::new_parser_ctx(parent, invoking_state,HeaderContextExt{
				libslVersion: None, version: None, language: None, url: None, 
				libraryName: None, 
				ph:PhantomData
			}),
		)
	}
}

pub trait HeaderContextAttrs<'input>: LibSLParserContext<'input> + BorrowMut<HeaderContextExt<'input>>{

/// Retrieves first TerminalNode corresponding to token LIBSL
/// Returns `None` if there is no child corresponding to token LIBSL
fn LIBSL(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(LIBSL, 0)
}
/// Retrieves all `TerminalNode`s corresponding to token SEMICOLON in current rule
fn SEMICOLON_all(&self) -> Vec<Rc<TerminalNode<'input,LibSLParserContextType>>>  where Self:Sized{
	self.get_tokens(SEMICOLON)
}
/// Retrieves 'i's TerminalNode corresponding to token SEMICOLON, starting from 0.
/// Returns `None` if number of children corresponding to token SEMICOLON is less or equal than `i`.
fn SEMICOLON(&self, i: usize) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(SEMICOLON, i)
}
/// Retrieves first TerminalNode corresponding to token LIBRARY
/// Returns `None` if there is no child corresponding to token LIBRARY
fn LIBRARY(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(LIBRARY, 0)
}
/// Retrieves all `TerminalNode`s corresponding to token StringLit in current rule
fn StringLit_all(&self) -> Vec<Rc<TerminalNode<'input,LibSLParserContextType>>>  where Self:Sized{
	self.get_tokens(StringLit)
}
/// Retrieves 'i's TerminalNode corresponding to token StringLit, starting from 0.
/// Returns `None` if number of children corresponding to token StringLit is less or equal than `i`.
fn StringLit(&self, i: usize) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(StringLit, i)
}
fn ident(&self) -> Option<Rc<IdentContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}
/// Retrieves first TerminalNode corresponding to token VERSION
/// Returns `None` if there is no child corresponding to token VERSION
fn VERSION(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(VERSION, 0)
}
/// Retrieves first TerminalNode corresponding to token LANGUAGE
/// Returns `None` if there is no child corresponding to token LANGUAGE
fn LANGUAGE(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(LANGUAGE, 0)
}
/// Retrieves first TerminalNode corresponding to token URL
/// Returns `None` if there is no child corresponding to token URL
fn URL(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(URL, 0)
}

}

impl<'input> HeaderContextAttrs<'input> for HeaderContext<'input>{}

impl<'input, I, H> LibSLParser<'input, I, H>
where
    I: TokenStream<'input, TF = LocalTokenFactory<'input> > + TidAble<'input>,
    H: ErrorStrategy<'input,BaseParserType<'input,I>>
{
	pub fn header(&mut self,)
	-> Result<Rc<HeaderContextAll<'input>>,ANTLRError> {
		let mut recog = self;
		let _parentctx = recog.ctx.take();
		let mut _localctx = HeaderContextExt::new(_parentctx.clone(), recog.base.get_state());
        recog.base.enter_rule(_localctx.clone(), 2, RULE_header);
        let mut _localctx: Rc<HeaderContextAll> = _localctx;
		let mut _la: isize = -1;
		let result: Result<(), ANTLRError> = (|| {

			//recog.base.enter_outer_alt(_localctx.clone(), 1);
			recog.base.enter_outer_alt(None, 1);
			{
			recog.base.set_state(217);
			recog.base.match_token(LIBSL,&mut recog.err_handler)?;

			recog.base.set_state(218);
			let tmp = recog.base.match_token(StringLit,&mut recog.err_handler)?;
			 cast_mut::<_,HeaderContext >(&mut _localctx).libslVersion = Some(tmp.clone());
			  

			recog.base.set_state(219);
			recog.base.match_token(SEMICOLON,&mut recog.err_handler)?;

			recog.base.set_state(220);
			recog.base.match_token(LIBRARY,&mut recog.err_handler)?;

			/*InvokeRule ident*/
			recog.base.set_state(221);
			let tmp = recog.ident()?;
			 cast_mut::<_,HeaderContext >(&mut _localctx).libraryName = Some(tmp.clone());
			  

			recog.base.set_state(224);
			recog.err_handler.sync(&mut recog.base)?;
			_la = recog.base.input.la(1);
			if _la==VERSION {
				{
				recog.base.set_state(222);
				recog.base.match_token(VERSION,&mut recog.err_handler)?;

				recog.base.set_state(223);
				let tmp = recog.base.match_token(StringLit,&mut recog.err_handler)?;
				 cast_mut::<_,HeaderContext >(&mut _localctx).version = Some(tmp.clone());
				  

				}
			}

			recog.base.set_state(228);
			recog.err_handler.sync(&mut recog.base)?;
			_la = recog.base.input.la(1);
			if _la==LANGUAGE {
				{
				recog.base.set_state(226);
				recog.base.match_token(LANGUAGE,&mut recog.err_handler)?;

				recog.base.set_state(227);
				let tmp = recog.base.match_token(StringLit,&mut recog.err_handler)?;
				 cast_mut::<_,HeaderContext >(&mut _localctx).language = Some(tmp.clone());
				  

				}
			}

			recog.base.set_state(232);
			recog.err_handler.sync(&mut recog.base)?;
			_la = recog.base.input.la(1);
			if _la==URL {
				{
				recog.base.set_state(230);
				recog.base.match_token(URL,&mut recog.err_handler)?;

				recog.base.set_state(231);
				let tmp = recog.base.match_token(StringLit,&mut recog.err_handler)?;
				 cast_mut::<_,HeaderContext >(&mut _localctx).url = Some(tmp.clone());
				  

				}
			}

			recog.base.set_state(234);
			recog.base.match_token(SEMICOLON,&mut recog.err_handler)?;

			}
			Ok(())
		})();
		match result {
		Ok(_)=>{},
        Err(e @ ANTLRError::FallThrough(_)) => return Err(e),
		Err(ref re) => {
				//_localctx.exception = re;
				recog.err_handler.report_error(&mut recog.base, re);
				recog.err_handler.recover(&mut recog.base, re)?;
			}
		}
		recog.base.exit_rule();

		Ok(_localctx)
	}
}
//------------------- globalDecl ----------------
#[derive(Debug)]
pub enum GlobalDeclContextAll<'input>{
	GlobalDeclFunctionContext(GlobalDeclFunctionContext<'input>),
	GlobalDeclIncludeContext(GlobalDeclIncludeContext<'input>),
	GlobalDeclTypeAliasContext(GlobalDeclTypeAliasContext<'input>),
	GlobalDeclAutomatonContext(GlobalDeclAutomatonContext<'input>),
	GlobalDeclActionContext(GlobalDeclActionContext<'input>),
	GlobalDeclAnnotationContext(GlobalDeclAnnotationContext<'input>),
	GlobalDeclImportContext(GlobalDeclImportContext<'input>),
	GlobalDeclPredContext(GlobalDeclPredContext<'input>),
	GlobalDeclVariableContext(GlobalDeclVariableContext<'input>),
	GlobalDeclSemanticTypeSectionContext(GlobalDeclSemanticTypeSectionContext<'input>),
	GlobalDeclStructContext(GlobalDeclStructContext<'input>),
	GlobalDeclEnumContext(GlobalDeclEnumContext<'input>),
	GlobalDeclProcContext(GlobalDeclProcContext<'input>),
Error(GlobalDeclContext<'input>)
}
antlr_rust::tid!{GlobalDeclContextAll<'a>}

impl<'input> antlr_rust::parser_rule_context::DerefSeal for GlobalDeclContextAll<'input>{}

impl<'input> LibSLParserContext<'input> for GlobalDeclContextAll<'input>{}

impl<'input> Deref for GlobalDeclContextAll<'input>{
	type Target = dyn GlobalDeclContextAttrs<'input> + 'input;
	fn deref(&self) -> &Self::Target{
		use GlobalDeclContextAll::*;
		match self{
			GlobalDeclFunctionContext(inner) => inner,
			GlobalDeclIncludeContext(inner) => inner,
			GlobalDeclTypeAliasContext(inner) => inner,
			GlobalDeclAutomatonContext(inner) => inner,
			GlobalDeclActionContext(inner) => inner,
			GlobalDeclAnnotationContext(inner) => inner,
			GlobalDeclImportContext(inner) => inner,
			GlobalDeclPredContext(inner) => inner,
			GlobalDeclVariableContext(inner) => inner,
			GlobalDeclSemanticTypeSectionContext(inner) => inner,
			GlobalDeclStructContext(inner) => inner,
			GlobalDeclEnumContext(inner) => inner,
			GlobalDeclProcContext(inner) => inner,
Error(inner) => inner
		}
	}
}
impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for GlobalDeclContextAll<'input>{
    fn enter(&self, listener: &mut (dyn LibSLParserListener<'input> + 'a)) { self.deref().enter(listener) }
    fn exit(&self, listener: &mut (dyn LibSLParserListener<'input> + 'a)) { self.deref().exit(listener) }
}



pub type GlobalDeclContext<'input> = BaseParserRuleContext<'input,GlobalDeclContextExt<'input>>;

#[derive(Clone)]
pub struct GlobalDeclContextExt<'input>{
ph:PhantomData<&'input str>
}

impl<'input> LibSLParserContext<'input> for GlobalDeclContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for GlobalDeclContext<'input>{
}

impl<'input> CustomRuleContext<'input> for GlobalDeclContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_globalDecl }
	//fn type_rule_index() -> usize where Self: Sized { RULE_globalDecl }
}
antlr_rust::tid!{GlobalDeclContextExt<'a>}

impl<'input> GlobalDeclContextExt<'input>{
	fn new(parent: Option<Rc<dyn LibSLParserContext<'input> + 'input > >, invoking_state: isize) -> Rc<GlobalDeclContextAll<'input>> {
		Rc::new(
		GlobalDeclContextAll::Error(
			BaseParserRuleContext::new_parser_ctx(parent, invoking_state,GlobalDeclContextExt{
				ph:PhantomData
			}),
		)
		)
	}
}

pub trait GlobalDeclContextAttrs<'input>: LibSLParserContext<'input> + BorrowMut<GlobalDeclContextExt<'input>>{


}

impl<'input> GlobalDeclContextAttrs<'input> for GlobalDeclContext<'input>{}

pub type GlobalDeclFunctionContext<'input> = BaseParserRuleContext<'input,GlobalDeclFunctionContextExt<'input>>;

pub trait GlobalDeclFunctionContextAttrs<'input>: LibSLParserContext<'input>{
	fn functionDecl(&self) -> Option<Rc<FunctionDeclContextAll<'input>>> where Self:Sized{
		self.child_of_type(0)
	}
}

impl<'input> GlobalDeclFunctionContextAttrs<'input> for GlobalDeclFunctionContext<'input>{}

pub struct GlobalDeclFunctionContextExt<'input>{
	__base:GlobalDeclContextExt<'input>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{GlobalDeclFunctionContextExt<'a>}

impl<'input> LibSLParserContext<'input> for GlobalDeclFunctionContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for GlobalDeclFunctionContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_GlobalDeclFunction(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_GlobalDeclFunction(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for GlobalDeclFunctionContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_globalDecl }
	//fn type_rule_index() -> usize where Self: Sized { RULE_globalDecl }
}

impl<'input> Borrow<GlobalDeclContextExt<'input>> for GlobalDeclFunctionContext<'input>{
	fn borrow(&self) -> &GlobalDeclContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<GlobalDeclContextExt<'input>> for GlobalDeclFunctionContext<'input>{
	fn borrow_mut(&mut self) -> &mut GlobalDeclContextExt<'input> { &mut self.__base }
}

impl<'input> GlobalDeclContextAttrs<'input> for GlobalDeclFunctionContext<'input> {}

impl<'input> GlobalDeclFunctionContextExt<'input>{
	fn new(ctx: &dyn GlobalDeclContextAttrs<'input>) -> Rc<GlobalDeclContextAll<'input>>  {
		Rc::new(
			GlobalDeclContextAll::GlobalDeclFunctionContext(
				BaseParserRuleContext::copy_from(ctx,GlobalDeclFunctionContextExt{
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type GlobalDeclIncludeContext<'input> = BaseParserRuleContext<'input,GlobalDeclIncludeContextExt<'input>>;

pub trait GlobalDeclIncludeContextAttrs<'input>: LibSLParserContext<'input>{
	fn includeDecl(&self) -> Option<Rc<IncludeDeclContextAll<'input>>> where Self:Sized{
		self.child_of_type(0)
	}
}

impl<'input> GlobalDeclIncludeContextAttrs<'input> for GlobalDeclIncludeContext<'input>{}

pub struct GlobalDeclIncludeContextExt<'input>{
	__base:GlobalDeclContextExt<'input>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{GlobalDeclIncludeContextExt<'a>}

impl<'input> LibSLParserContext<'input> for GlobalDeclIncludeContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for GlobalDeclIncludeContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_GlobalDeclInclude(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_GlobalDeclInclude(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for GlobalDeclIncludeContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_globalDecl }
	//fn type_rule_index() -> usize where Self: Sized { RULE_globalDecl }
}

impl<'input> Borrow<GlobalDeclContextExt<'input>> for GlobalDeclIncludeContext<'input>{
	fn borrow(&self) -> &GlobalDeclContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<GlobalDeclContextExt<'input>> for GlobalDeclIncludeContext<'input>{
	fn borrow_mut(&mut self) -> &mut GlobalDeclContextExt<'input> { &mut self.__base }
}

impl<'input> GlobalDeclContextAttrs<'input> for GlobalDeclIncludeContext<'input> {}

impl<'input> GlobalDeclIncludeContextExt<'input>{
	fn new(ctx: &dyn GlobalDeclContextAttrs<'input>) -> Rc<GlobalDeclContextAll<'input>>  {
		Rc::new(
			GlobalDeclContextAll::GlobalDeclIncludeContext(
				BaseParserRuleContext::copy_from(ctx,GlobalDeclIncludeContextExt{
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type GlobalDeclTypeAliasContext<'input> = BaseParserRuleContext<'input,GlobalDeclTypeAliasContextExt<'input>>;

pub trait GlobalDeclTypeAliasContextAttrs<'input>: LibSLParserContext<'input>{
	fn typeAliasDecl(&self) -> Option<Rc<TypeAliasDeclContextAll<'input>>> where Self:Sized{
		self.child_of_type(0)
	}
}

impl<'input> GlobalDeclTypeAliasContextAttrs<'input> for GlobalDeclTypeAliasContext<'input>{}

pub struct GlobalDeclTypeAliasContextExt<'input>{
	__base:GlobalDeclContextExt<'input>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{GlobalDeclTypeAliasContextExt<'a>}

impl<'input> LibSLParserContext<'input> for GlobalDeclTypeAliasContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for GlobalDeclTypeAliasContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_GlobalDeclTypeAlias(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_GlobalDeclTypeAlias(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for GlobalDeclTypeAliasContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_globalDecl }
	//fn type_rule_index() -> usize where Self: Sized { RULE_globalDecl }
}

impl<'input> Borrow<GlobalDeclContextExt<'input>> for GlobalDeclTypeAliasContext<'input>{
	fn borrow(&self) -> &GlobalDeclContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<GlobalDeclContextExt<'input>> for GlobalDeclTypeAliasContext<'input>{
	fn borrow_mut(&mut self) -> &mut GlobalDeclContextExt<'input> { &mut self.__base }
}

impl<'input> GlobalDeclContextAttrs<'input> for GlobalDeclTypeAliasContext<'input> {}

impl<'input> GlobalDeclTypeAliasContextExt<'input>{
	fn new(ctx: &dyn GlobalDeclContextAttrs<'input>) -> Rc<GlobalDeclContextAll<'input>>  {
		Rc::new(
			GlobalDeclContextAll::GlobalDeclTypeAliasContext(
				BaseParserRuleContext::copy_from(ctx,GlobalDeclTypeAliasContextExt{
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type GlobalDeclAutomatonContext<'input> = BaseParserRuleContext<'input,GlobalDeclAutomatonContextExt<'input>>;

pub trait GlobalDeclAutomatonContextAttrs<'input>: LibSLParserContext<'input>{
	fn automatonDecl(&self) -> Option<Rc<AutomatonDeclContextAll<'input>>> where Self:Sized{
		self.child_of_type(0)
	}
}

impl<'input> GlobalDeclAutomatonContextAttrs<'input> for GlobalDeclAutomatonContext<'input>{}

pub struct GlobalDeclAutomatonContextExt<'input>{
	__base:GlobalDeclContextExt<'input>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{GlobalDeclAutomatonContextExt<'a>}

impl<'input> LibSLParserContext<'input> for GlobalDeclAutomatonContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for GlobalDeclAutomatonContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_GlobalDeclAutomaton(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_GlobalDeclAutomaton(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for GlobalDeclAutomatonContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_globalDecl }
	//fn type_rule_index() -> usize where Self: Sized { RULE_globalDecl }
}

impl<'input> Borrow<GlobalDeclContextExt<'input>> for GlobalDeclAutomatonContext<'input>{
	fn borrow(&self) -> &GlobalDeclContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<GlobalDeclContextExt<'input>> for GlobalDeclAutomatonContext<'input>{
	fn borrow_mut(&mut self) -> &mut GlobalDeclContextExt<'input> { &mut self.__base }
}

impl<'input> GlobalDeclContextAttrs<'input> for GlobalDeclAutomatonContext<'input> {}

impl<'input> GlobalDeclAutomatonContextExt<'input>{
	fn new(ctx: &dyn GlobalDeclContextAttrs<'input>) -> Rc<GlobalDeclContextAll<'input>>  {
		Rc::new(
			GlobalDeclContextAll::GlobalDeclAutomatonContext(
				BaseParserRuleContext::copy_from(ctx,GlobalDeclAutomatonContextExt{
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type GlobalDeclActionContext<'input> = BaseParserRuleContext<'input,GlobalDeclActionContextExt<'input>>;

pub trait GlobalDeclActionContextAttrs<'input>: LibSLParserContext<'input>{
	fn actionDecl(&self) -> Option<Rc<ActionDeclContextAll<'input>>> where Self:Sized{
		self.child_of_type(0)
	}
}

impl<'input> GlobalDeclActionContextAttrs<'input> for GlobalDeclActionContext<'input>{}

pub struct GlobalDeclActionContextExt<'input>{
	__base:GlobalDeclContextExt<'input>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{GlobalDeclActionContextExt<'a>}

impl<'input> LibSLParserContext<'input> for GlobalDeclActionContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for GlobalDeclActionContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_GlobalDeclAction(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_GlobalDeclAction(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for GlobalDeclActionContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_globalDecl }
	//fn type_rule_index() -> usize where Self: Sized { RULE_globalDecl }
}

impl<'input> Borrow<GlobalDeclContextExt<'input>> for GlobalDeclActionContext<'input>{
	fn borrow(&self) -> &GlobalDeclContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<GlobalDeclContextExt<'input>> for GlobalDeclActionContext<'input>{
	fn borrow_mut(&mut self) -> &mut GlobalDeclContextExt<'input> { &mut self.__base }
}

impl<'input> GlobalDeclContextAttrs<'input> for GlobalDeclActionContext<'input> {}

impl<'input> GlobalDeclActionContextExt<'input>{
	fn new(ctx: &dyn GlobalDeclContextAttrs<'input>) -> Rc<GlobalDeclContextAll<'input>>  {
		Rc::new(
			GlobalDeclContextAll::GlobalDeclActionContext(
				BaseParserRuleContext::copy_from(ctx,GlobalDeclActionContextExt{
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type GlobalDeclAnnotationContext<'input> = BaseParserRuleContext<'input,GlobalDeclAnnotationContextExt<'input>>;

pub trait GlobalDeclAnnotationContextAttrs<'input>: LibSLParserContext<'input>{
	fn annotationDecl(&self) -> Option<Rc<AnnotationDeclContextAll<'input>>> where Self:Sized{
		self.child_of_type(0)
	}
}

impl<'input> GlobalDeclAnnotationContextAttrs<'input> for GlobalDeclAnnotationContext<'input>{}

pub struct GlobalDeclAnnotationContextExt<'input>{
	__base:GlobalDeclContextExt<'input>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{GlobalDeclAnnotationContextExt<'a>}

impl<'input> LibSLParserContext<'input> for GlobalDeclAnnotationContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for GlobalDeclAnnotationContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_GlobalDeclAnnotation(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_GlobalDeclAnnotation(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for GlobalDeclAnnotationContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_globalDecl }
	//fn type_rule_index() -> usize where Self: Sized { RULE_globalDecl }
}

impl<'input> Borrow<GlobalDeclContextExt<'input>> for GlobalDeclAnnotationContext<'input>{
	fn borrow(&self) -> &GlobalDeclContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<GlobalDeclContextExt<'input>> for GlobalDeclAnnotationContext<'input>{
	fn borrow_mut(&mut self) -> &mut GlobalDeclContextExt<'input> { &mut self.__base }
}

impl<'input> GlobalDeclContextAttrs<'input> for GlobalDeclAnnotationContext<'input> {}

impl<'input> GlobalDeclAnnotationContextExt<'input>{
	fn new(ctx: &dyn GlobalDeclContextAttrs<'input>) -> Rc<GlobalDeclContextAll<'input>>  {
		Rc::new(
			GlobalDeclContextAll::GlobalDeclAnnotationContext(
				BaseParserRuleContext::copy_from(ctx,GlobalDeclAnnotationContextExt{
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type GlobalDeclImportContext<'input> = BaseParserRuleContext<'input,GlobalDeclImportContextExt<'input>>;

pub trait GlobalDeclImportContextAttrs<'input>: LibSLParserContext<'input>{
	fn importDecl(&self) -> Option<Rc<ImportDeclContextAll<'input>>> where Self:Sized{
		self.child_of_type(0)
	}
}

impl<'input> GlobalDeclImportContextAttrs<'input> for GlobalDeclImportContext<'input>{}

pub struct GlobalDeclImportContextExt<'input>{
	__base:GlobalDeclContextExt<'input>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{GlobalDeclImportContextExt<'a>}

impl<'input> LibSLParserContext<'input> for GlobalDeclImportContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for GlobalDeclImportContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_GlobalDeclImport(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_GlobalDeclImport(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for GlobalDeclImportContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_globalDecl }
	//fn type_rule_index() -> usize where Self: Sized { RULE_globalDecl }
}

impl<'input> Borrow<GlobalDeclContextExt<'input>> for GlobalDeclImportContext<'input>{
	fn borrow(&self) -> &GlobalDeclContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<GlobalDeclContextExt<'input>> for GlobalDeclImportContext<'input>{
	fn borrow_mut(&mut self) -> &mut GlobalDeclContextExt<'input> { &mut self.__base }
}

impl<'input> GlobalDeclContextAttrs<'input> for GlobalDeclImportContext<'input> {}

impl<'input> GlobalDeclImportContextExt<'input>{
	fn new(ctx: &dyn GlobalDeclContextAttrs<'input>) -> Rc<GlobalDeclContextAll<'input>>  {
		Rc::new(
			GlobalDeclContextAll::GlobalDeclImportContext(
				BaseParserRuleContext::copy_from(ctx,GlobalDeclImportContextExt{
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type GlobalDeclPredContext<'input> = BaseParserRuleContext<'input,GlobalDeclPredContextExt<'input>>;

pub trait GlobalDeclPredContextAttrs<'input>: LibSLParserContext<'input>{
	fn predDecl(&self) -> Option<Rc<PredDeclContextAll<'input>>> where Self:Sized{
		self.child_of_type(0)
	}
}

impl<'input> GlobalDeclPredContextAttrs<'input> for GlobalDeclPredContext<'input>{}

pub struct GlobalDeclPredContextExt<'input>{
	__base:GlobalDeclContextExt<'input>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{GlobalDeclPredContextExt<'a>}

impl<'input> LibSLParserContext<'input> for GlobalDeclPredContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for GlobalDeclPredContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_GlobalDeclPred(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_GlobalDeclPred(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for GlobalDeclPredContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_globalDecl }
	//fn type_rule_index() -> usize where Self: Sized { RULE_globalDecl }
}

impl<'input> Borrow<GlobalDeclContextExt<'input>> for GlobalDeclPredContext<'input>{
	fn borrow(&self) -> &GlobalDeclContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<GlobalDeclContextExt<'input>> for GlobalDeclPredContext<'input>{
	fn borrow_mut(&mut self) -> &mut GlobalDeclContextExt<'input> { &mut self.__base }
}

impl<'input> GlobalDeclContextAttrs<'input> for GlobalDeclPredContext<'input> {}

impl<'input> GlobalDeclPredContextExt<'input>{
	fn new(ctx: &dyn GlobalDeclContextAttrs<'input>) -> Rc<GlobalDeclContextAll<'input>>  {
		Rc::new(
			GlobalDeclContextAll::GlobalDeclPredContext(
				BaseParserRuleContext::copy_from(ctx,GlobalDeclPredContextExt{
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type GlobalDeclVariableContext<'input> = BaseParserRuleContext<'input,GlobalDeclVariableContextExt<'input>>;

pub trait GlobalDeclVariableContextAttrs<'input>: LibSLParserContext<'input>{
	fn variableDecl(&self) -> Option<Rc<VariableDeclContextAll<'input>>> where Self:Sized{
		self.child_of_type(0)
	}
}

impl<'input> GlobalDeclVariableContextAttrs<'input> for GlobalDeclVariableContext<'input>{}

pub struct GlobalDeclVariableContextExt<'input>{
	__base:GlobalDeclContextExt<'input>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{GlobalDeclVariableContextExt<'a>}

impl<'input> LibSLParserContext<'input> for GlobalDeclVariableContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for GlobalDeclVariableContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_GlobalDeclVariable(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_GlobalDeclVariable(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for GlobalDeclVariableContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_globalDecl }
	//fn type_rule_index() -> usize where Self: Sized { RULE_globalDecl }
}

impl<'input> Borrow<GlobalDeclContextExt<'input>> for GlobalDeclVariableContext<'input>{
	fn borrow(&self) -> &GlobalDeclContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<GlobalDeclContextExt<'input>> for GlobalDeclVariableContext<'input>{
	fn borrow_mut(&mut self) -> &mut GlobalDeclContextExt<'input> { &mut self.__base }
}

impl<'input> GlobalDeclContextAttrs<'input> for GlobalDeclVariableContext<'input> {}

impl<'input> GlobalDeclVariableContextExt<'input>{
	fn new(ctx: &dyn GlobalDeclContextAttrs<'input>) -> Rc<GlobalDeclContextAll<'input>>  {
		Rc::new(
			GlobalDeclContextAll::GlobalDeclVariableContext(
				BaseParserRuleContext::copy_from(ctx,GlobalDeclVariableContextExt{
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type GlobalDeclSemanticTypeSectionContext<'input> = BaseParserRuleContext<'input,GlobalDeclSemanticTypeSectionContextExt<'input>>;

pub trait GlobalDeclSemanticTypeSectionContextAttrs<'input>: LibSLParserContext<'input>{
	fn semanticTypeSectionDecl(&self) -> Option<Rc<SemanticTypeSectionDeclContextAll<'input>>> where Self:Sized{
		self.child_of_type(0)
	}
}

impl<'input> GlobalDeclSemanticTypeSectionContextAttrs<'input> for GlobalDeclSemanticTypeSectionContext<'input>{}

pub struct GlobalDeclSemanticTypeSectionContextExt<'input>{
	__base:GlobalDeclContextExt<'input>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{GlobalDeclSemanticTypeSectionContextExt<'a>}

impl<'input> LibSLParserContext<'input> for GlobalDeclSemanticTypeSectionContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for GlobalDeclSemanticTypeSectionContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_GlobalDeclSemanticTypeSection(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_GlobalDeclSemanticTypeSection(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for GlobalDeclSemanticTypeSectionContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_globalDecl }
	//fn type_rule_index() -> usize where Self: Sized { RULE_globalDecl }
}

impl<'input> Borrow<GlobalDeclContextExt<'input>> for GlobalDeclSemanticTypeSectionContext<'input>{
	fn borrow(&self) -> &GlobalDeclContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<GlobalDeclContextExt<'input>> for GlobalDeclSemanticTypeSectionContext<'input>{
	fn borrow_mut(&mut self) -> &mut GlobalDeclContextExt<'input> { &mut self.__base }
}

impl<'input> GlobalDeclContextAttrs<'input> for GlobalDeclSemanticTypeSectionContext<'input> {}

impl<'input> GlobalDeclSemanticTypeSectionContextExt<'input>{
	fn new(ctx: &dyn GlobalDeclContextAttrs<'input>) -> Rc<GlobalDeclContextAll<'input>>  {
		Rc::new(
			GlobalDeclContextAll::GlobalDeclSemanticTypeSectionContext(
				BaseParserRuleContext::copy_from(ctx,GlobalDeclSemanticTypeSectionContextExt{
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type GlobalDeclStructContext<'input> = BaseParserRuleContext<'input,GlobalDeclStructContextExt<'input>>;

pub trait GlobalDeclStructContextAttrs<'input>: LibSLParserContext<'input>{
	fn structDecl(&self) -> Option<Rc<StructDeclContextAll<'input>>> where Self:Sized{
		self.child_of_type(0)
	}
}

impl<'input> GlobalDeclStructContextAttrs<'input> for GlobalDeclStructContext<'input>{}

pub struct GlobalDeclStructContextExt<'input>{
	__base:GlobalDeclContextExt<'input>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{GlobalDeclStructContextExt<'a>}

impl<'input> LibSLParserContext<'input> for GlobalDeclStructContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for GlobalDeclStructContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_GlobalDeclStruct(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_GlobalDeclStruct(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for GlobalDeclStructContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_globalDecl }
	//fn type_rule_index() -> usize where Self: Sized { RULE_globalDecl }
}

impl<'input> Borrow<GlobalDeclContextExt<'input>> for GlobalDeclStructContext<'input>{
	fn borrow(&self) -> &GlobalDeclContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<GlobalDeclContextExt<'input>> for GlobalDeclStructContext<'input>{
	fn borrow_mut(&mut self) -> &mut GlobalDeclContextExt<'input> { &mut self.__base }
}

impl<'input> GlobalDeclContextAttrs<'input> for GlobalDeclStructContext<'input> {}

impl<'input> GlobalDeclStructContextExt<'input>{
	fn new(ctx: &dyn GlobalDeclContextAttrs<'input>) -> Rc<GlobalDeclContextAll<'input>>  {
		Rc::new(
			GlobalDeclContextAll::GlobalDeclStructContext(
				BaseParserRuleContext::copy_from(ctx,GlobalDeclStructContextExt{
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type GlobalDeclEnumContext<'input> = BaseParserRuleContext<'input,GlobalDeclEnumContextExt<'input>>;

pub trait GlobalDeclEnumContextAttrs<'input>: LibSLParserContext<'input>{
	fn enumDecl(&self) -> Option<Rc<EnumDeclContextAll<'input>>> where Self:Sized{
		self.child_of_type(0)
	}
}

impl<'input> GlobalDeclEnumContextAttrs<'input> for GlobalDeclEnumContext<'input>{}

pub struct GlobalDeclEnumContextExt<'input>{
	__base:GlobalDeclContextExt<'input>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{GlobalDeclEnumContextExt<'a>}

impl<'input> LibSLParserContext<'input> for GlobalDeclEnumContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for GlobalDeclEnumContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_GlobalDeclEnum(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_GlobalDeclEnum(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for GlobalDeclEnumContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_globalDecl }
	//fn type_rule_index() -> usize where Self: Sized { RULE_globalDecl }
}

impl<'input> Borrow<GlobalDeclContextExt<'input>> for GlobalDeclEnumContext<'input>{
	fn borrow(&self) -> &GlobalDeclContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<GlobalDeclContextExt<'input>> for GlobalDeclEnumContext<'input>{
	fn borrow_mut(&mut self) -> &mut GlobalDeclContextExt<'input> { &mut self.__base }
}

impl<'input> GlobalDeclContextAttrs<'input> for GlobalDeclEnumContext<'input> {}

impl<'input> GlobalDeclEnumContextExt<'input>{
	fn new(ctx: &dyn GlobalDeclContextAttrs<'input>) -> Rc<GlobalDeclContextAll<'input>>  {
		Rc::new(
			GlobalDeclContextAll::GlobalDeclEnumContext(
				BaseParserRuleContext::copy_from(ctx,GlobalDeclEnumContextExt{
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type GlobalDeclProcContext<'input> = BaseParserRuleContext<'input,GlobalDeclProcContextExt<'input>>;

pub trait GlobalDeclProcContextAttrs<'input>: LibSLParserContext<'input>{
	fn procDecl(&self) -> Option<Rc<ProcDeclContextAll<'input>>> where Self:Sized{
		self.child_of_type(0)
	}
}

impl<'input> GlobalDeclProcContextAttrs<'input> for GlobalDeclProcContext<'input>{}

pub struct GlobalDeclProcContextExt<'input>{
	__base:GlobalDeclContextExt<'input>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{GlobalDeclProcContextExt<'a>}

impl<'input> LibSLParserContext<'input> for GlobalDeclProcContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for GlobalDeclProcContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_GlobalDeclProc(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_GlobalDeclProc(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for GlobalDeclProcContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_globalDecl }
	//fn type_rule_index() -> usize where Self: Sized { RULE_globalDecl }
}

impl<'input> Borrow<GlobalDeclContextExt<'input>> for GlobalDeclProcContext<'input>{
	fn borrow(&self) -> &GlobalDeclContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<GlobalDeclContextExt<'input>> for GlobalDeclProcContext<'input>{
	fn borrow_mut(&mut self) -> &mut GlobalDeclContextExt<'input> { &mut self.__base }
}

impl<'input> GlobalDeclContextAttrs<'input> for GlobalDeclProcContext<'input> {}

impl<'input> GlobalDeclProcContextExt<'input>{
	fn new(ctx: &dyn GlobalDeclContextAttrs<'input>) -> Rc<GlobalDeclContextAll<'input>>  {
		Rc::new(
			GlobalDeclContextAll::GlobalDeclProcContext(
				BaseParserRuleContext::copy_from(ctx,GlobalDeclProcContextExt{
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

impl<'input, I, H> LibSLParser<'input, I, H>
where
    I: TokenStream<'input, TF = LocalTokenFactory<'input> > + TidAble<'input>,
    H: ErrorStrategy<'input,BaseParserType<'input,I>>
{
	pub fn globalDecl(&mut self,)
	-> Result<Rc<GlobalDeclContextAll<'input>>,ANTLRError> {
		let mut recog = self;
		let _parentctx = recog.ctx.take();
		let mut _localctx = GlobalDeclContextExt::new(_parentctx.clone(), recog.base.get_state());
        recog.base.enter_rule(_localctx.clone(), 4, RULE_globalDecl);
        let mut _localctx: Rc<GlobalDeclContextAll> = _localctx;
		let result: Result<(), ANTLRError> = (|| {

			recog.base.set_state(249);
			recog.err_handler.sync(&mut recog.base)?;
			match  recog.interpreter.adaptive_predict(5,&mut recog.base)? {
				1 =>{
					let tmp = GlobalDeclImportContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 1);
					_localctx = tmp;
					{
					/*InvokeRule importDecl*/
					recog.base.set_state(236);
					recog.importDecl()?;

					}
				}
			,
				2 =>{
					let tmp = GlobalDeclIncludeContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 2);
					_localctx = tmp;
					{
					/*InvokeRule includeDecl*/
					recog.base.set_state(237);
					recog.includeDecl()?;

					}
				}
			,
				3 =>{
					let tmp = GlobalDeclSemanticTypeSectionContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 3);
					_localctx = tmp;
					{
					/*InvokeRule semanticTypeSectionDecl*/
					recog.base.set_state(238);
					recog.semanticTypeSectionDecl()?;

					}
				}
			,
				4 =>{
					let tmp = GlobalDeclTypeAliasContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 4);
					_localctx = tmp;
					{
					/*InvokeRule typeAliasDecl*/
					recog.base.set_state(239);
					recog.typeAliasDecl()?;

					}
				}
			,
				5 =>{
					let tmp = GlobalDeclStructContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 5);
					_localctx = tmp;
					{
					/*InvokeRule structDecl*/
					recog.base.set_state(240);
					recog.structDecl()?;

					}
				}
			,
				6 =>{
					let tmp = GlobalDeclEnumContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 6);
					_localctx = tmp;
					{
					/*InvokeRule enumDecl*/
					recog.base.set_state(241);
					recog.enumDecl()?;

					}
				}
			,
				7 =>{
					let tmp = GlobalDeclAnnotationContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 7);
					_localctx = tmp;
					{
					/*InvokeRule annotationDecl*/
					recog.base.set_state(242);
					recog.annotationDecl()?;

					}
				}
			,
				8 =>{
					let tmp = GlobalDeclActionContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 8);
					_localctx = tmp;
					{
					/*InvokeRule actionDecl*/
					recog.base.set_state(243);
					recog.actionDecl()?;

					}
				}
			,
				9 =>{
					let tmp = GlobalDeclAutomatonContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 9);
					_localctx = tmp;
					{
					/*InvokeRule automatonDecl*/
					recog.base.set_state(244);
					recog.automatonDecl()?;

					}
				}
			,
				10 =>{
					let tmp = GlobalDeclFunctionContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 10);
					_localctx = tmp;
					{
					/*InvokeRule functionDecl*/
					recog.base.set_state(245);
					recog.functionDecl()?;

					}
				}
			,
				11 =>{
					let tmp = GlobalDeclProcContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 11);
					_localctx = tmp;
					{
					/*InvokeRule procDecl*/
					recog.base.set_state(246);
					recog.procDecl()?;

					}
				}
			,
				12 =>{
					let tmp = GlobalDeclPredContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 12);
					_localctx = tmp;
					{
					/*InvokeRule predDecl*/
					recog.base.set_state(247);
					recog.predDecl()?;

					}
				}
			,
				13 =>{
					let tmp = GlobalDeclVariableContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 13);
					_localctx = tmp;
					{
					/*InvokeRule variableDecl*/
					recog.base.set_state(248);
					recog.variableDecl()?;

					}
				}

				_ => {}
			}
			Ok(())
		})();
		match result {
		Ok(_)=>{},
        Err(e @ ANTLRError::FallThrough(_)) => return Err(e),
		Err(ref re) => {
				//_localctx.exception = re;
				recog.err_handler.report_error(&mut recog.base, re);
				recog.err_handler.recover(&mut recog.base, re)?;
			}
		}
		recog.base.exit_rule();

		Ok(_localctx)
	}
}
//------------------- importDecl ----------------
pub type ImportDeclContextAll<'input> = ImportDeclContext<'input>;


pub type ImportDeclContext<'input> = BaseParserRuleContext<'input,ImportDeclContextExt<'input>>;

#[derive(Clone)]
pub struct ImportDeclContextExt<'input>{
ph:PhantomData<&'input str>
}

impl<'input> LibSLParserContext<'input> for ImportDeclContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for ImportDeclContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_importDecl(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_importDecl(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for ImportDeclContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_importDecl }
	//fn type_rule_index() -> usize where Self: Sized { RULE_importDecl }
}
antlr_rust::tid!{ImportDeclContextExt<'a>}

impl<'input> ImportDeclContextExt<'input>{
	fn new(parent: Option<Rc<dyn LibSLParserContext<'input> + 'input > >, invoking_state: isize) -> Rc<ImportDeclContextAll<'input>> {
		Rc::new(
			BaseParserRuleContext::new_parser_ctx(parent, invoking_state,ImportDeclContextExt{
				ph:PhantomData
			}),
		)
	}
}

pub trait ImportDeclContextAttrs<'input>: LibSLParserContext<'input> + BorrowMut<ImportDeclContextExt<'input>>{

/// Retrieves first TerminalNode corresponding to token IMPORT
/// Returns `None` if there is no child corresponding to token IMPORT
fn IMPORT(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(IMPORT, 0)
}
fn path(&self) -> Option<Rc<PathContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}
/// Retrieves first TerminalNode corresponding to token SEMICOLON
/// Returns `None` if there is no child corresponding to token SEMICOLON
fn SEMICOLON(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(SEMICOLON, 0)
}

}

impl<'input> ImportDeclContextAttrs<'input> for ImportDeclContext<'input>{}

impl<'input, I, H> LibSLParser<'input, I, H>
where
    I: TokenStream<'input, TF = LocalTokenFactory<'input> > + TidAble<'input>,
    H: ErrorStrategy<'input,BaseParserType<'input,I>>
{
	pub fn importDecl(&mut self,)
	-> Result<Rc<ImportDeclContextAll<'input>>,ANTLRError> {
		let mut recog = self;
		let _parentctx = recog.ctx.take();
		let mut _localctx = ImportDeclContextExt::new(_parentctx.clone(), recog.base.get_state());
        recog.base.enter_rule(_localctx.clone(), 6, RULE_importDecl);
        let mut _localctx: Rc<ImportDeclContextAll> = _localctx;
		let result: Result<(), ANTLRError> = (|| {

			//recog.base.enter_outer_alt(_localctx.clone(), 1);
			recog.base.enter_outer_alt(None, 1);
			{
			recog.base.set_state(251);
			recog.base.match_token(IMPORT,&mut recog.err_handler)?;

			/*InvokeRule path*/
			recog.base.set_state(252);
			recog.path()?;

			recog.base.set_state(253);
			recog.base.match_token(SEMICOLON,&mut recog.err_handler)?;

			}
			Ok(())
		})();
		match result {
		Ok(_)=>{},
        Err(e @ ANTLRError::FallThrough(_)) => return Err(e),
		Err(ref re) => {
				//_localctx.exception = re;
				recog.err_handler.report_error(&mut recog.base, re);
				recog.err_handler.recover(&mut recog.base, re)?;
			}
		}
		recog.base.exit_rule();

		Ok(_localctx)
	}
}
//------------------- includeDecl ----------------
pub type IncludeDeclContextAll<'input> = IncludeDeclContext<'input>;


pub type IncludeDeclContext<'input> = BaseParserRuleContext<'input,IncludeDeclContextExt<'input>>;

#[derive(Clone)]
pub struct IncludeDeclContextExt<'input>{
ph:PhantomData<&'input str>
}

impl<'input> LibSLParserContext<'input> for IncludeDeclContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for IncludeDeclContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_includeDecl(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_includeDecl(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for IncludeDeclContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_includeDecl }
	//fn type_rule_index() -> usize where Self: Sized { RULE_includeDecl }
}
antlr_rust::tid!{IncludeDeclContextExt<'a>}

impl<'input> IncludeDeclContextExt<'input>{
	fn new(parent: Option<Rc<dyn LibSLParserContext<'input> + 'input > >, invoking_state: isize) -> Rc<IncludeDeclContextAll<'input>> {
		Rc::new(
			BaseParserRuleContext::new_parser_ctx(parent, invoking_state,IncludeDeclContextExt{
				ph:PhantomData
			}),
		)
	}
}

pub trait IncludeDeclContextAttrs<'input>: LibSLParserContext<'input> + BorrowMut<IncludeDeclContextExt<'input>>{

/// Retrieves first TerminalNode corresponding to token INCLUDE
/// Returns `None` if there is no child corresponding to token INCLUDE
fn INCLUDE(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(INCLUDE, 0)
}
fn path(&self) -> Option<Rc<PathContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}
/// Retrieves first TerminalNode corresponding to token SEMICOLON
/// Returns `None` if there is no child corresponding to token SEMICOLON
fn SEMICOLON(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(SEMICOLON, 0)
}

}

impl<'input> IncludeDeclContextAttrs<'input> for IncludeDeclContext<'input>{}

impl<'input, I, H> LibSLParser<'input, I, H>
where
    I: TokenStream<'input, TF = LocalTokenFactory<'input> > + TidAble<'input>,
    H: ErrorStrategy<'input,BaseParserType<'input,I>>
{
	pub fn includeDecl(&mut self,)
	-> Result<Rc<IncludeDeclContextAll<'input>>,ANTLRError> {
		let mut recog = self;
		let _parentctx = recog.ctx.take();
		let mut _localctx = IncludeDeclContextExt::new(_parentctx.clone(), recog.base.get_state());
        recog.base.enter_rule(_localctx.clone(), 8, RULE_includeDecl);
        let mut _localctx: Rc<IncludeDeclContextAll> = _localctx;
		let result: Result<(), ANTLRError> = (|| {

			//recog.base.enter_outer_alt(_localctx.clone(), 1);
			recog.base.enter_outer_alt(None, 1);
			{
			recog.base.set_state(255);
			recog.base.match_token(INCLUDE,&mut recog.err_handler)?;

			/*InvokeRule path*/
			recog.base.set_state(256);
			recog.path()?;

			recog.base.set_state(257);
			recog.base.match_token(SEMICOLON,&mut recog.err_handler)?;

			}
			Ok(())
		})();
		match result {
		Ok(_)=>{},
        Err(e @ ANTLRError::FallThrough(_)) => return Err(e),
		Err(ref re) => {
				//_localctx.exception = re;
				recog.err_handler.report_error(&mut recog.base, re);
				recog.err_handler.recover(&mut recog.base, re)?;
			}
		}
		recog.base.exit_rule();

		Ok(_localctx)
	}
}
//------------------- path ----------------
#[derive(Debug)]
pub enum PathContextAll<'input>{
	PathBareContext(PathBareContext<'input>),
	PathStringLitContext(PathStringLitContext<'input>),
Error(PathContext<'input>)
}
antlr_rust::tid!{PathContextAll<'a>}

impl<'input> antlr_rust::parser_rule_context::DerefSeal for PathContextAll<'input>{}

impl<'input> LibSLParserContext<'input> for PathContextAll<'input>{}

impl<'input> Deref for PathContextAll<'input>{
	type Target = dyn PathContextAttrs<'input> + 'input;
	fn deref(&self) -> &Self::Target{
		use PathContextAll::*;
		match self{
			PathBareContext(inner) => inner,
			PathStringLitContext(inner) => inner,
Error(inner) => inner
		}
	}
}
impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for PathContextAll<'input>{
    fn enter(&self, listener: &mut (dyn LibSLParserListener<'input> + 'a)) { self.deref().enter(listener) }
    fn exit(&self, listener: &mut (dyn LibSLParserListener<'input> + 'a)) { self.deref().exit(listener) }
}



pub type PathContext<'input> = BaseParserRuleContext<'input,PathContextExt<'input>>;

#[derive(Clone)]
pub struct PathContextExt<'input>{
ph:PhantomData<&'input str>
}

impl<'input> LibSLParserContext<'input> for PathContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for PathContext<'input>{
}

impl<'input> CustomRuleContext<'input> for PathContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_path }
	//fn type_rule_index() -> usize where Self: Sized { RULE_path }
}
antlr_rust::tid!{PathContextExt<'a>}

impl<'input> PathContextExt<'input>{
	fn new(parent: Option<Rc<dyn LibSLParserContext<'input> + 'input > >, invoking_state: isize) -> Rc<PathContextAll<'input>> {
		Rc::new(
		PathContextAll::Error(
			BaseParserRuleContext::new_parser_ctx(parent, invoking_state,PathContextExt{
				ph:PhantomData
			}),
		)
		)
	}
}

pub trait PathContextAttrs<'input>: LibSLParserContext<'input> + BorrowMut<PathContextExt<'input>>{


}

impl<'input> PathContextAttrs<'input> for PathContext<'input>{}

pub type PathBareContext<'input> = BaseParserRuleContext<'input,PathBareContextExt<'input>>;

pub trait PathBareContextAttrs<'input>: LibSLParserContext<'input>{
	/// Retrieves first TerminalNode corresponding to token BarePath
	/// Returns `None` if there is no child corresponding to token BarePath
	fn BarePath(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(BarePath, 0)
	}
}

impl<'input> PathBareContextAttrs<'input> for PathBareContext<'input>{}

pub struct PathBareContextExt<'input>{
	__base:PathContextExt<'input>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{PathBareContextExt<'a>}

impl<'input> LibSLParserContext<'input> for PathBareContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for PathBareContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_PathBare(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_PathBare(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for PathBareContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_path }
	//fn type_rule_index() -> usize where Self: Sized { RULE_path }
}

impl<'input> Borrow<PathContextExt<'input>> for PathBareContext<'input>{
	fn borrow(&self) -> &PathContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<PathContextExt<'input>> for PathBareContext<'input>{
	fn borrow_mut(&mut self) -> &mut PathContextExt<'input> { &mut self.__base }
}

impl<'input> PathContextAttrs<'input> for PathBareContext<'input> {}

impl<'input> PathBareContextExt<'input>{
	fn new(ctx: &dyn PathContextAttrs<'input>) -> Rc<PathContextAll<'input>>  {
		Rc::new(
			PathContextAll::PathBareContext(
				BaseParserRuleContext::copy_from(ctx,PathBareContextExt{
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type PathStringLitContext<'input> = BaseParserRuleContext<'input,PathStringLitContextExt<'input>>;

pub trait PathStringLitContextAttrs<'input>: LibSLParserContext<'input>{
	/// Retrieves first TerminalNode corresponding to token StringLit
	/// Returns `None` if there is no child corresponding to token StringLit
	fn StringLit(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(StringLit, 0)
	}
}

impl<'input> PathStringLitContextAttrs<'input> for PathStringLitContext<'input>{}

pub struct PathStringLitContextExt<'input>{
	__base:PathContextExt<'input>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{PathStringLitContextExt<'a>}

impl<'input> LibSLParserContext<'input> for PathStringLitContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for PathStringLitContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_PathStringLit(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_PathStringLit(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for PathStringLitContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_path }
	//fn type_rule_index() -> usize where Self: Sized { RULE_path }
}

impl<'input> Borrow<PathContextExt<'input>> for PathStringLitContext<'input>{
	fn borrow(&self) -> &PathContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<PathContextExt<'input>> for PathStringLitContext<'input>{
	fn borrow_mut(&mut self) -> &mut PathContextExt<'input> { &mut self.__base }
}

impl<'input> PathContextAttrs<'input> for PathStringLitContext<'input> {}

impl<'input> PathStringLitContextExt<'input>{
	fn new(ctx: &dyn PathContextAttrs<'input>) -> Rc<PathContextAll<'input>>  {
		Rc::new(
			PathContextAll::PathStringLitContext(
				BaseParserRuleContext::copy_from(ctx,PathStringLitContextExt{
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

impl<'input, I, H> LibSLParser<'input, I, H>
where
    I: TokenStream<'input, TF = LocalTokenFactory<'input> > + TidAble<'input>,
    H: ErrorStrategy<'input,BaseParserType<'input,I>>
{
	pub fn path(&mut self,)
	-> Result<Rc<PathContextAll<'input>>,ANTLRError> {
		let mut recog = self;
		let _parentctx = recog.ctx.take();
		let mut _localctx = PathContextExt::new(_parentctx.clone(), recog.base.get_state());
        recog.base.enter_rule(_localctx.clone(), 10, RULE_path);
        let mut _localctx: Rc<PathContextAll> = _localctx;
		let result: Result<(), ANTLRError> = (|| {

			recog.base.set_state(261);
			recog.err_handler.sync(&mut recog.base)?;
			match recog.base.input.la(1) {
			 StringLit 
				=> {
					let tmp = PathStringLitContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 1);
					_localctx = tmp;
					{
					recog.base.set_state(259);
					recog.base.match_token(StringLit,&mut recog.err_handler)?;

					}
				}

			 BarePath 
				=> {
					let tmp = PathBareContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 2);
					_localctx = tmp;
					{
					recog.base.set_state(260);
					recog.base.match_token(BarePath,&mut recog.err_handler)?;

					}
				}

				_ => Err(ANTLRError::NoAltError(NoViableAltError::new(&mut recog.base)))?
			}
			Ok(())
		})();
		match result {
		Ok(_)=>{},
        Err(e @ ANTLRError::FallThrough(_)) => return Err(e),
		Err(ref re) => {
				//_localctx.exception = re;
				recog.err_handler.report_error(&mut recog.base, re);
				recog.err_handler.recover(&mut recog.base, re)?;
			}
		}
		recog.base.exit_rule();

		Ok(_localctx)
	}
}
//------------------- semanticTypeSectionDecl ----------------
pub type SemanticTypeSectionDeclContextAll<'input> = SemanticTypeSectionDeclContext<'input>;


pub type SemanticTypeSectionDeclContext<'input> = BaseParserRuleContext<'input,SemanticTypeSectionDeclContextExt<'input>>;

#[derive(Clone)]
pub struct SemanticTypeSectionDeclContextExt<'input>{
	pub semanticTypeDecl: Option<Rc<SemanticTypeDeclContextAll<'input>>>,
	pub decls:Vec<Rc<SemanticTypeDeclContextAll<'input>>>,
ph:PhantomData<&'input str>
}

impl<'input> LibSLParserContext<'input> for SemanticTypeSectionDeclContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for SemanticTypeSectionDeclContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_semanticTypeSectionDecl(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_semanticTypeSectionDecl(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for SemanticTypeSectionDeclContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_semanticTypeSectionDecl }
	//fn type_rule_index() -> usize where Self: Sized { RULE_semanticTypeSectionDecl }
}
antlr_rust::tid!{SemanticTypeSectionDeclContextExt<'a>}

impl<'input> SemanticTypeSectionDeclContextExt<'input>{
	fn new(parent: Option<Rc<dyn LibSLParserContext<'input> + 'input > >, invoking_state: isize) -> Rc<SemanticTypeSectionDeclContextAll<'input>> {
		Rc::new(
			BaseParserRuleContext::new_parser_ctx(parent, invoking_state,SemanticTypeSectionDeclContextExt{
				semanticTypeDecl: None, 
				decls: Vec::new(), 
				ph:PhantomData
			}),
		)
	}
}

pub trait SemanticTypeSectionDeclContextAttrs<'input>: LibSLParserContext<'input> + BorrowMut<SemanticTypeSectionDeclContextExt<'input>>{

/// Retrieves first TerminalNode corresponding to token TYPES
/// Returns `None` if there is no child corresponding to token TYPES
fn TYPES(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(TYPES, 0)
}
/// Retrieves first TerminalNode corresponding to token L_BRACE
/// Returns `None` if there is no child corresponding to token L_BRACE
fn L_BRACE(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(L_BRACE, 0)
}
/// Retrieves first TerminalNode corresponding to token R_BRACE
/// Returns `None` if there is no child corresponding to token R_BRACE
fn R_BRACE(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(R_BRACE, 0)
}
fn semanticTypeDecl_all(&self) ->  Vec<Rc<SemanticTypeDeclContextAll<'input>>> where Self:Sized{
	self.children_of_type()
}
fn semanticTypeDecl(&self, i: usize) -> Option<Rc<SemanticTypeDeclContextAll<'input>>> where Self:Sized{
	self.child_of_type(i)
}

}

impl<'input> SemanticTypeSectionDeclContextAttrs<'input> for SemanticTypeSectionDeclContext<'input>{}

impl<'input, I, H> LibSLParser<'input, I, H>
where
    I: TokenStream<'input, TF = LocalTokenFactory<'input> > + TidAble<'input>,
    H: ErrorStrategy<'input,BaseParserType<'input,I>>
{
	pub fn semanticTypeSectionDecl(&mut self,)
	-> Result<Rc<SemanticTypeSectionDeclContextAll<'input>>,ANTLRError> {
		let mut recog = self;
		let _parentctx = recog.ctx.take();
		let mut _localctx = SemanticTypeSectionDeclContextExt::new(_parentctx.clone(), recog.base.get_state());
        recog.base.enter_rule(_localctx.clone(), 12, RULE_semanticTypeSectionDecl);
        let mut _localctx: Rc<SemanticTypeSectionDeclContextAll> = _localctx;
		let mut _la: isize = -1;
		let result: Result<(), ANTLRError> = (|| {

			//recog.base.enter_outer_alt(_localctx.clone(), 1);
			recog.base.enter_outer_alt(None, 1);
			{
			recog.base.set_state(263);
			recog.base.match_token(TYPES,&mut recog.err_handler)?;

			recog.base.set_state(264);
			recog.base.match_token(L_BRACE,&mut recog.err_handler)?;

			recog.base.set_state(268);
			recog.err_handler.sync(&mut recog.base)?;
			_la = recog.base.input.la(1);
			while ((((_la - 86)) & !0x3f) == 0 && ((1usize << (_la - 86)) & 647) != 0) {
				{
				{
				/*InvokeRule semanticTypeDecl*/
				recog.base.set_state(265);
				let tmp = recog.semanticTypeDecl()?;
				 cast_mut::<_,SemanticTypeSectionDeclContext >(&mut _localctx).semanticTypeDecl = Some(tmp.clone());
				  

				let temp =  cast_mut::<_,SemanticTypeSectionDeclContext >(&mut _localctx).semanticTypeDecl.clone().unwrap()
				 ;
				 cast_mut::<_,SemanticTypeSectionDeclContext >(&mut _localctx).decls.push(temp);
				  
				}
				}
				recog.base.set_state(270);
				recog.err_handler.sync(&mut recog.base)?;
				_la = recog.base.input.la(1);
			}
			recog.base.set_state(271);
			recog.base.match_token(R_BRACE,&mut recog.err_handler)?;

			}
			Ok(())
		})();
		match result {
		Ok(_)=>{},
        Err(e @ ANTLRError::FallThrough(_)) => return Err(e),
		Err(ref re) => {
				//_localctx.exception = re;
				recog.err_handler.report_error(&mut recog.base, re);
				recog.err_handler.recover(&mut recog.base, re)?;
			}
		}
		recog.base.exit_rule();

		Ok(_localctx)
	}
}
//------------------- semanticTypeDecl ----------------
pub type SemanticTypeDeclContextAll<'input> = SemanticTypeDeclContext<'input>;


pub type SemanticTypeDeclContext<'input> = BaseParserRuleContext<'input,SemanticTypeDeclContextExt<'input>>;

#[derive(Clone)]
pub struct SemanticTypeDeclContextExt<'input>{
	pub annotation: Option<Rc<AnnotationContextAll<'input>>>,
	pub annotations:Vec<Rc<AnnotationContextAll<'input>>>,
	pub typeName: Option<Rc<QualifiedTypeNameContextAll<'input>>>,
	pub realType: Option<Rc<TypeExprContextAll<'input>>>,
ph:PhantomData<&'input str>
}

impl<'input> LibSLParserContext<'input> for SemanticTypeDeclContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for SemanticTypeDeclContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_semanticTypeDecl(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_semanticTypeDecl(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for SemanticTypeDeclContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_semanticTypeDecl }
	//fn type_rule_index() -> usize where Self: Sized { RULE_semanticTypeDecl }
}
antlr_rust::tid!{SemanticTypeDeclContextExt<'a>}

impl<'input> SemanticTypeDeclContextExt<'input>{
	fn new(parent: Option<Rc<dyn LibSLParserContext<'input> + 'input > >, invoking_state: isize) -> Rc<SemanticTypeDeclContextAll<'input>> {
		Rc::new(
			BaseParserRuleContext::new_parser_ctx(parent, invoking_state,SemanticTypeDeclContextExt{
				annotation: None, typeName: None, realType: None, 
				annotations: Vec::new(), 
				ph:PhantomData
			}),
		)
	}
}

pub trait SemanticTypeDeclContextAttrs<'input>: LibSLParserContext<'input> + BorrowMut<SemanticTypeDeclContextExt<'input>>{

/// Retrieves first TerminalNode corresponding to token L_PAREN
/// Returns `None` if there is no child corresponding to token L_PAREN
fn L_PAREN(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(L_PAREN, 0)
}
/// Retrieves first TerminalNode corresponding to token R_PAREN
/// Returns `None` if there is no child corresponding to token R_PAREN
fn R_PAREN(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(R_PAREN, 0)
}
fn semanticTypeDef(&self) -> Option<Rc<SemanticTypeDefContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}
fn qualifiedTypeName(&self) -> Option<Rc<QualifiedTypeNameContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}
fn typeExpr(&self) -> Option<Rc<TypeExprContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}
fn annotation_all(&self) ->  Vec<Rc<AnnotationContextAll<'input>>> where Self:Sized{
	self.children_of_type()
}
fn annotation(&self, i: usize) -> Option<Rc<AnnotationContextAll<'input>>> where Self:Sized{
	self.child_of_type(i)
}

}

impl<'input> SemanticTypeDeclContextAttrs<'input> for SemanticTypeDeclContext<'input>{}

impl<'input, I, H> LibSLParser<'input, I, H>
where
    I: TokenStream<'input, TF = LocalTokenFactory<'input> > + TidAble<'input>,
    H: ErrorStrategy<'input,BaseParserType<'input,I>>
{
	pub fn semanticTypeDecl(&mut self,)
	-> Result<Rc<SemanticTypeDeclContextAll<'input>>,ANTLRError> {
		let mut recog = self;
		let _parentctx = recog.ctx.take();
		let mut _localctx = SemanticTypeDeclContextExt::new(_parentctx.clone(), recog.base.get_state());
        recog.base.enter_rule(_localctx.clone(), 14, RULE_semanticTypeDecl);
        let mut _localctx: Rc<SemanticTypeDeclContextAll> = _localctx;
		let mut _la: isize = -1;
		let result: Result<(), ANTLRError> = (|| {

			//recog.base.enter_outer_alt(_localctx.clone(), 1);
			recog.base.enter_outer_alt(None, 1);
			{
			recog.base.set_state(276);
			recog.err_handler.sync(&mut recog.base)?;
			_la = recog.base.input.la(1);
			while _la==AT {
				{
				{
				/*InvokeRule annotation*/
				recog.base.set_state(273);
				let tmp = recog.annotation()?;
				 cast_mut::<_,SemanticTypeDeclContext >(&mut _localctx).annotation = Some(tmp.clone());
				  

				let temp =  cast_mut::<_,SemanticTypeDeclContext >(&mut _localctx).annotation.clone().unwrap()
				 ;
				 cast_mut::<_,SemanticTypeDeclContext >(&mut _localctx).annotations.push(temp);
				  
				}
				}
				recog.base.set_state(278);
				recog.err_handler.sync(&mut recog.base)?;
				_la = recog.base.input.la(1);
			}
			/*InvokeRule qualifiedTypeName*/
			recog.base.set_state(279);
			let tmp = recog.qualifiedTypeName()?;
			 cast_mut::<_,SemanticTypeDeclContext >(&mut _localctx).typeName = Some(tmp.clone());
			  

			recog.base.set_state(280);
			recog.base.match_token(L_PAREN,&mut recog.err_handler)?;

			/*InvokeRule typeExpr*/
			recog.base.set_state(281);
			let tmp = recog.typeExpr_rec(0)?;
			 cast_mut::<_,SemanticTypeDeclContext >(&mut _localctx).realType = Some(tmp.clone());
			  

			recog.base.set_state(282);
			recog.base.match_token(R_PAREN,&mut recog.err_handler)?;

			/*InvokeRule semanticTypeDef*/
			recog.base.set_state(283);
			recog.semanticTypeDef()?;

			}
			Ok(())
		})();
		match result {
		Ok(_)=>{},
        Err(e @ ANTLRError::FallThrough(_)) => return Err(e),
		Err(ref re) => {
				//_localctx.exception = re;
				recog.err_handler.report_error(&mut recog.base, re);
				recog.err_handler.recover(&mut recog.base, re)?;
			}
		}
		recog.base.exit_rule();

		Ok(_localctx)
	}
}
//------------------- semanticTypeDef ----------------
#[derive(Debug)]
pub enum SemanticTypeDefContextAll<'input>{
	SemanticTypeDefSimpleContext(SemanticTypeDefSimpleContext<'input>),
	SemanticTypeDefEnumContext(SemanticTypeDefEnumContext<'input>),
Error(SemanticTypeDefContext<'input>)
}
antlr_rust::tid!{SemanticTypeDefContextAll<'a>}

impl<'input> antlr_rust::parser_rule_context::DerefSeal for SemanticTypeDefContextAll<'input>{}

impl<'input> LibSLParserContext<'input> for SemanticTypeDefContextAll<'input>{}

impl<'input> Deref for SemanticTypeDefContextAll<'input>{
	type Target = dyn SemanticTypeDefContextAttrs<'input> + 'input;
	fn deref(&self) -> &Self::Target{
		use SemanticTypeDefContextAll::*;
		match self{
			SemanticTypeDefSimpleContext(inner) => inner,
			SemanticTypeDefEnumContext(inner) => inner,
Error(inner) => inner
		}
	}
}
impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for SemanticTypeDefContextAll<'input>{
    fn enter(&self, listener: &mut (dyn LibSLParserListener<'input> + 'a)) { self.deref().enter(listener) }
    fn exit(&self, listener: &mut (dyn LibSLParserListener<'input> + 'a)) { self.deref().exit(listener) }
}



pub type SemanticTypeDefContext<'input> = BaseParserRuleContext<'input,SemanticTypeDefContextExt<'input>>;

#[derive(Clone)]
pub struct SemanticTypeDefContextExt<'input>{
ph:PhantomData<&'input str>
}

impl<'input> LibSLParserContext<'input> for SemanticTypeDefContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for SemanticTypeDefContext<'input>{
}

impl<'input> CustomRuleContext<'input> for SemanticTypeDefContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_semanticTypeDef }
	//fn type_rule_index() -> usize where Self: Sized { RULE_semanticTypeDef }
}
antlr_rust::tid!{SemanticTypeDefContextExt<'a>}

impl<'input> SemanticTypeDefContextExt<'input>{
	fn new(parent: Option<Rc<dyn LibSLParserContext<'input> + 'input > >, invoking_state: isize) -> Rc<SemanticTypeDefContextAll<'input>> {
		Rc::new(
		SemanticTypeDefContextAll::Error(
			BaseParserRuleContext::new_parser_ctx(parent, invoking_state,SemanticTypeDefContextExt{
				ph:PhantomData
			}),
		)
		)
	}
}

pub trait SemanticTypeDefContextAttrs<'input>: LibSLParserContext<'input> + BorrowMut<SemanticTypeDefContextExt<'input>>{


}

impl<'input> SemanticTypeDefContextAttrs<'input> for SemanticTypeDefContext<'input>{}

pub type SemanticTypeDefSimpleContext<'input> = BaseParserRuleContext<'input,SemanticTypeDefSimpleContextExt<'input>>;

pub trait SemanticTypeDefSimpleContextAttrs<'input>: LibSLParserContext<'input>{
	/// Retrieves first TerminalNode corresponding to token SEMICOLON
	/// Returns `None` if there is no child corresponding to token SEMICOLON
	fn SEMICOLON(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(SEMICOLON, 0)
	}
}

impl<'input> SemanticTypeDefSimpleContextAttrs<'input> for SemanticTypeDefSimpleContext<'input>{}

pub struct SemanticTypeDefSimpleContextExt<'input>{
	__base:SemanticTypeDefContextExt<'input>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{SemanticTypeDefSimpleContextExt<'a>}

impl<'input> LibSLParserContext<'input> for SemanticTypeDefSimpleContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for SemanticTypeDefSimpleContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_SemanticTypeDefSimple(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_SemanticTypeDefSimple(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for SemanticTypeDefSimpleContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_semanticTypeDef }
	//fn type_rule_index() -> usize where Self: Sized { RULE_semanticTypeDef }
}

impl<'input> Borrow<SemanticTypeDefContextExt<'input>> for SemanticTypeDefSimpleContext<'input>{
	fn borrow(&self) -> &SemanticTypeDefContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<SemanticTypeDefContextExt<'input>> for SemanticTypeDefSimpleContext<'input>{
	fn borrow_mut(&mut self) -> &mut SemanticTypeDefContextExt<'input> { &mut self.__base }
}

impl<'input> SemanticTypeDefContextAttrs<'input> for SemanticTypeDefSimpleContext<'input> {}

impl<'input> SemanticTypeDefSimpleContextExt<'input>{
	fn new(ctx: &dyn SemanticTypeDefContextAttrs<'input>) -> Rc<SemanticTypeDefContextAll<'input>>  {
		Rc::new(
			SemanticTypeDefContextAll::SemanticTypeDefSimpleContext(
				BaseParserRuleContext::copy_from(ctx,SemanticTypeDefSimpleContextExt{
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type SemanticTypeDefEnumContext<'input> = BaseParserRuleContext<'input,SemanticTypeDefEnumContextExt<'input>>;

pub trait SemanticTypeDefEnumContextAttrs<'input>: LibSLParserContext<'input>{
	/// Retrieves first TerminalNode corresponding to token L_BRACE
	/// Returns `None` if there is no child corresponding to token L_BRACE
	fn L_BRACE(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(L_BRACE, 0)
	}
	/// Retrieves first TerminalNode corresponding to token R_BRACE
	/// Returns `None` if there is no child corresponding to token R_BRACE
	fn R_BRACE(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(R_BRACE, 0)
	}
	fn enumSemanticTypeValue_all(&self) ->  Vec<Rc<EnumSemanticTypeValueContextAll<'input>>> where Self:Sized{
		self.children_of_type()
	}
	fn enumSemanticTypeValue(&self, i: usize) -> Option<Rc<EnumSemanticTypeValueContextAll<'input>>> where Self:Sized{
		self.child_of_type(i)
	}
}

impl<'input> SemanticTypeDefEnumContextAttrs<'input> for SemanticTypeDefEnumContext<'input>{}

pub struct SemanticTypeDefEnumContextExt<'input>{
	__base:SemanticTypeDefContextExt<'input>,
	pub enumSemanticTypeValue: Option<Rc<EnumSemanticTypeValueContextAll<'input>>>,
	pub values:Vec<Rc<EnumSemanticTypeValueContextAll<'input>>>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{SemanticTypeDefEnumContextExt<'a>}

impl<'input> LibSLParserContext<'input> for SemanticTypeDefEnumContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for SemanticTypeDefEnumContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_SemanticTypeDefEnum(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_SemanticTypeDefEnum(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for SemanticTypeDefEnumContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_semanticTypeDef }
	//fn type_rule_index() -> usize where Self: Sized { RULE_semanticTypeDef }
}

impl<'input> Borrow<SemanticTypeDefContextExt<'input>> for SemanticTypeDefEnumContext<'input>{
	fn borrow(&self) -> &SemanticTypeDefContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<SemanticTypeDefContextExt<'input>> for SemanticTypeDefEnumContext<'input>{
	fn borrow_mut(&mut self) -> &mut SemanticTypeDefContextExt<'input> { &mut self.__base }
}

impl<'input> SemanticTypeDefContextAttrs<'input> for SemanticTypeDefEnumContext<'input> {}

impl<'input> SemanticTypeDefEnumContextExt<'input>{
	fn new(ctx: &dyn SemanticTypeDefContextAttrs<'input>) -> Rc<SemanticTypeDefContextAll<'input>>  {
		Rc::new(
			SemanticTypeDefContextAll::SemanticTypeDefEnumContext(
				BaseParserRuleContext::copy_from(ctx,SemanticTypeDefEnumContextExt{
        			enumSemanticTypeValue:None, 
        			values:Vec::new(), 
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

impl<'input, I, H> LibSLParser<'input, I, H>
where
    I: TokenStream<'input, TF = LocalTokenFactory<'input> > + TidAble<'input>,
    H: ErrorStrategy<'input,BaseParserType<'input,I>>
{
	pub fn semanticTypeDef(&mut self,)
	-> Result<Rc<SemanticTypeDefContextAll<'input>>,ANTLRError> {
		let mut recog = self;
		let _parentctx = recog.ctx.take();
		let mut _localctx = SemanticTypeDefContextExt::new(_parentctx.clone(), recog.base.get_state());
        recog.base.enter_rule(_localctx.clone(), 16, RULE_semanticTypeDef);
        let mut _localctx: Rc<SemanticTypeDefContextAll> = _localctx;
		let mut _la: isize = -1;
		let result: Result<(), ANTLRError> = (|| {

			recog.base.set_state(294);
			recog.err_handler.sync(&mut recog.base)?;
			match recog.base.input.la(1) {
			 SEMICOLON 
				=> {
					let tmp = SemanticTypeDefSimpleContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 1);
					_localctx = tmp;
					{
					recog.base.set_state(285);
					recog.base.match_token(SEMICOLON,&mut recog.err_handler)?;

					}
				}

			 L_BRACE 
				=> {
					let tmp = SemanticTypeDefEnumContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 2);
					_localctx = tmp;
					{
					recog.base.set_state(286);
					recog.base.match_token(L_BRACE,&mut recog.err_handler)?;

					recog.base.set_state(290);
					recog.err_handler.sync(&mut recog.base)?;
					_la = recog.base.input.la(1);
					while ((((_la - 86)) & !0x3f) == 0 && ((1usize << (_la - 86)) & 519) != 0) {
						{
						{
						/*InvokeRule enumSemanticTypeValue*/
						recog.base.set_state(287);
						let tmp = recog.enumSemanticTypeValue()?;
						if let SemanticTypeDefContextAll::SemanticTypeDefEnumContext(ctx) = cast_mut::<_,SemanticTypeDefContextAll >(&mut _localctx){
						ctx.enumSemanticTypeValue = Some(tmp.clone()); } else {unreachable!("cant cast");}  

						let temp = if let SemanticTypeDefContextAll::SemanticTypeDefEnumContext(ctx) = cast_mut::<_,SemanticTypeDefContextAll >(&mut _localctx){
						ctx.enumSemanticTypeValue.clone().unwrap() } else {unreachable!("cant cast");} ;
						if let SemanticTypeDefContextAll::SemanticTypeDefEnumContext(ctx) = cast_mut::<_,SemanticTypeDefContextAll >(&mut _localctx){
						ctx.values.push(temp); } else {unreachable!("cant cast");}  
						}
						}
						recog.base.set_state(292);
						recog.err_handler.sync(&mut recog.base)?;
						_la = recog.base.input.la(1);
					}
					recog.base.set_state(293);
					recog.base.match_token(R_BRACE,&mut recog.err_handler)?;

					}
				}

				_ => Err(ANTLRError::NoAltError(NoViableAltError::new(&mut recog.base)))?
			}
			Ok(())
		})();
		match result {
		Ok(_)=>{},
        Err(e @ ANTLRError::FallThrough(_)) => return Err(e),
		Err(ref re) => {
				//_localctx.exception = re;
				recog.err_handler.report_error(&mut recog.base, re);
				recog.err_handler.recover(&mut recog.base, re)?;
			}
		}
		recog.base.exit_rule();

		Ok(_localctx)
	}
}
//------------------- enumSemanticTypeValue ----------------
pub type EnumSemanticTypeValueContextAll<'input> = EnumSemanticTypeValueContext<'input>;


pub type EnumSemanticTypeValueContext<'input> = BaseParserRuleContext<'input,EnumSemanticTypeValueContextExt<'input>>;

#[derive(Clone)]
pub struct EnumSemanticTypeValueContextExt<'input>{
	pub name: Option<Rc<IdentContextAll<'input>>>,
	pub value: Option<Rc<AtomicExprContextAll<'input>>>,
ph:PhantomData<&'input str>
}

impl<'input> LibSLParserContext<'input> for EnumSemanticTypeValueContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for EnumSemanticTypeValueContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_enumSemanticTypeValue(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_enumSemanticTypeValue(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for EnumSemanticTypeValueContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_enumSemanticTypeValue }
	//fn type_rule_index() -> usize where Self: Sized { RULE_enumSemanticTypeValue }
}
antlr_rust::tid!{EnumSemanticTypeValueContextExt<'a>}

impl<'input> EnumSemanticTypeValueContextExt<'input>{
	fn new(parent: Option<Rc<dyn LibSLParserContext<'input> + 'input > >, invoking_state: isize) -> Rc<EnumSemanticTypeValueContextAll<'input>> {
		Rc::new(
			BaseParserRuleContext::new_parser_ctx(parent, invoking_state,EnumSemanticTypeValueContextExt{
				name: None, value: None, 
				ph:PhantomData
			}),
		)
	}
}

pub trait EnumSemanticTypeValueContextAttrs<'input>: LibSLParserContext<'input> + BorrowMut<EnumSemanticTypeValueContextExt<'input>>{

/// Retrieves first TerminalNode corresponding to token COLON
/// Returns `None` if there is no child corresponding to token COLON
fn COLON(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(COLON, 0)
}
/// Retrieves first TerminalNode corresponding to token SEMICOLON
/// Returns `None` if there is no child corresponding to token SEMICOLON
fn SEMICOLON(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(SEMICOLON, 0)
}
fn ident(&self) -> Option<Rc<IdentContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}
fn atomicExpr(&self) -> Option<Rc<AtomicExprContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}

}

impl<'input> EnumSemanticTypeValueContextAttrs<'input> for EnumSemanticTypeValueContext<'input>{}

impl<'input, I, H> LibSLParser<'input, I, H>
where
    I: TokenStream<'input, TF = LocalTokenFactory<'input> > + TidAble<'input>,
    H: ErrorStrategy<'input,BaseParserType<'input,I>>
{
	pub fn enumSemanticTypeValue(&mut self,)
	-> Result<Rc<EnumSemanticTypeValueContextAll<'input>>,ANTLRError> {
		let mut recog = self;
		let _parentctx = recog.ctx.take();
		let mut _localctx = EnumSemanticTypeValueContextExt::new(_parentctx.clone(), recog.base.get_state());
        recog.base.enter_rule(_localctx.clone(), 18, RULE_enumSemanticTypeValue);
        let mut _localctx: Rc<EnumSemanticTypeValueContextAll> = _localctx;
		let result: Result<(), ANTLRError> = (|| {

			//recog.base.enter_outer_alt(_localctx.clone(), 1);
			recog.base.enter_outer_alt(None, 1);
			{
			/*InvokeRule ident*/
			recog.base.set_state(296);
			let tmp = recog.ident()?;
			 cast_mut::<_,EnumSemanticTypeValueContext >(&mut _localctx).name = Some(tmp.clone());
			  

			recog.base.set_state(297);
			recog.base.match_token(COLON,&mut recog.err_handler)?;

			/*InvokeRule atomicExpr*/
			recog.base.set_state(298);
			let tmp = recog.atomicExpr()?;
			 cast_mut::<_,EnumSemanticTypeValueContext >(&mut _localctx).value = Some(tmp.clone());
			  

			recog.base.set_state(299);
			recog.base.match_token(SEMICOLON,&mut recog.err_handler)?;

			}
			Ok(())
		})();
		match result {
		Ok(_)=>{},
        Err(e @ ANTLRError::FallThrough(_)) => return Err(e),
		Err(ref re) => {
				//_localctx.exception = re;
				recog.err_handler.report_error(&mut recog.base, re);
				recog.err_handler.recover(&mut recog.base, re)?;
			}
		}
		recog.base.exit_rule();

		Ok(_localctx)
	}
}
//------------------- typeAliasDecl ----------------
pub type TypeAliasDeclContextAll<'input> = TypeAliasDeclContext<'input>;


pub type TypeAliasDeclContext<'input> = BaseParserRuleContext<'input,TypeAliasDeclContextExt<'input>>;

#[derive(Clone)]
pub struct TypeAliasDeclContextExt<'input>{
	pub annotation: Option<Rc<AnnotationContextAll<'input>>>,
	pub annotations:Vec<Rc<AnnotationContextAll<'input>>>,
	pub typeName: Option<Rc<QualifiedTypeNameContextAll<'input>>>,
	pub def: Option<Rc<TypeExprContextAll<'input>>>,
ph:PhantomData<&'input str>
}

impl<'input> LibSLParserContext<'input> for TypeAliasDeclContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for TypeAliasDeclContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_typeAliasDecl(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_typeAliasDecl(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for TypeAliasDeclContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_typeAliasDecl }
	//fn type_rule_index() -> usize where Self: Sized { RULE_typeAliasDecl }
}
antlr_rust::tid!{TypeAliasDeclContextExt<'a>}

impl<'input> TypeAliasDeclContextExt<'input>{
	fn new(parent: Option<Rc<dyn LibSLParserContext<'input> + 'input > >, invoking_state: isize) -> Rc<TypeAliasDeclContextAll<'input>> {
		Rc::new(
			BaseParserRuleContext::new_parser_ctx(parent, invoking_state,TypeAliasDeclContextExt{
				annotation: None, typeName: None, def: None, 
				annotations: Vec::new(), 
				ph:PhantomData
			}),
		)
	}
}

pub trait TypeAliasDeclContextAttrs<'input>: LibSLParserContext<'input> + BorrowMut<TypeAliasDeclContextExt<'input>>{

/// Retrieves first TerminalNode corresponding to token TYPEALIAS
/// Returns `None` if there is no child corresponding to token TYPEALIAS
fn TYPEALIAS(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(TYPEALIAS, 0)
}
/// Retrieves first TerminalNode corresponding to token EQ
/// Returns `None` if there is no child corresponding to token EQ
fn EQ(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(EQ, 0)
}
/// Retrieves first TerminalNode corresponding to token SEMICOLON
/// Returns `None` if there is no child corresponding to token SEMICOLON
fn SEMICOLON(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(SEMICOLON, 0)
}
fn qualifiedTypeName(&self) -> Option<Rc<QualifiedTypeNameContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}
fn typeExpr(&self) -> Option<Rc<TypeExprContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}
fn annotation_all(&self) ->  Vec<Rc<AnnotationContextAll<'input>>> where Self:Sized{
	self.children_of_type()
}
fn annotation(&self, i: usize) -> Option<Rc<AnnotationContextAll<'input>>> where Self:Sized{
	self.child_of_type(i)
}

}

impl<'input> TypeAliasDeclContextAttrs<'input> for TypeAliasDeclContext<'input>{}

impl<'input, I, H> LibSLParser<'input, I, H>
where
    I: TokenStream<'input, TF = LocalTokenFactory<'input> > + TidAble<'input>,
    H: ErrorStrategy<'input,BaseParserType<'input,I>>
{
	pub fn typeAliasDecl(&mut self,)
	-> Result<Rc<TypeAliasDeclContextAll<'input>>,ANTLRError> {
		let mut recog = self;
		let _parentctx = recog.ctx.take();
		let mut _localctx = TypeAliasDeclContextExt::new(_parentctx.clone(), recog.base.get_state());
        recog.base.enter_rule(_localctx.clone(), 20, RULE_typeAliasDecl);
        let mut _localctx: Rc<TypeAliasDeclContextAll> = _localctx;
		let mut _la: isize = -1;
		let result: Result<(), ANTLRError> = (|| {

			//recog.base.enter_outer_alt(_localctx.clone(), 1);
			recog.base.enter_outer_alt(None, 1);
			{
			recog.base.set_state(304);
			recog.err_handler.sync(&mut recog.base)?;
			_la = recog.base.input.la(1);
			while _la==AT {
				{
				{
				/*InvokeRule annotation*/
				recog.base.set_state(301);
				let tmp = recog.annotation()?;
				 cast_mut::<_,TypeAliasDeclContext >(&mut _localctx).annotation = Some(tmp.clone());
				  

				let temp =  cast_mut::<_,TypeAliasDeclContext >(&mut _localctx).annotation.clone().unwrap()
				 ;
				 cast_mut::<_,TypeAliasDeclContext >(&mut _localctx).annotations.push(temp);
				  
				}
				}
				recog.base.set_state(306);
				recog.err_handler.sync(&mut recog.base)?;
				_la = recog.base.input.la(1);
			}
			recog.base.set_state(307);
			recog.base.match_token(TYPEALIAS,&mut recog.err_handler)?;

			/*InvokeRule qualifiedTypeName*/
			recog.base.set_state(308);
			let tmp = recog.qualifiedTypeName()?;
			 cast_mut::<_,TypeAliasDeclContext >(&mut _localctx).typeName = Some(tmp.clone());
			  

			recog.base.set_state(309);
			recog.base.match_token(EQ,&mut recog.err_handler)?;

			/*InvokeRule typeExpr*/
			recog.base.set_state(310);
			let tmp = recog.typeExpr_rec(0)?;
			 cast_mut::<_,TypeAliasDeclContext >(&mut _localctx).def = Some(tmp.clone());
			  

			recog.base.set_state(311);
			recog.base.match_token(SEMICOLON,&mut recog.err_handler)?;

			}
			Ok(())
		})();
		match result {
		Ok(_)=>{},
        Err(e @ ANTLRError::FallThrough(_)) => return Err(e),
		Err(ref re) => {
				//_localctx.exception = re;
				recog.err_handler.report_error(&mut recog.base, re);
				recog.err_handler.recover(&mut recog.base, re)?;
			}
		}
		recog.base.exit_rule();

		Ok(_localctx)
	}
}
//------------------- structDecl ----------------
pub type StructDeclContextAll<'input> = StructDeclContext<'input>;


pub type StructDeclContext<'input> = BaseParserRuleContext<'input,StructDeclContextExt<'input>>;

#[derive(Clone)]
pub struct StructDeclContextExt<'input>{
	pub annotation: Option<Rc<AnnotationContextAll<'input>>>,
	pub annotations:Vec<Rc<AnnotationContextAll<'input>>>,
	pub typeName: Option<Rc<QualifiedTypeNameContextAll<'input>>>,
	pub targetType: Option<Rc<StructTargetTypeContextAll<'input>>>,
	pub typeConstraints: Option<Rc<WhereClauseContextAll<'input>>>,
	pub structDefDecl: Option<Rc<StructDefDeclContextAll<'input>>>,
	pub decls:Vec<Rc<StructDefDeclContextAll<'input>>>,
ph:PhantomData<&'input str>
}

impl<'input> LibSLParserContext<'input> for StructDeclContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for StructDeclContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_structDecl(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_structDecl(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for StructDeclContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_structDecl }
	//fn type_rule_index() -> usize where Self: Sized { RULE_structDecl }
}
antlr_rust::tid!{StructDeclContextExt<'a>}

impl<'input> StructDeclContextExt<'input>{
	fn new(parent: Option<Rc<dyn LibSLParserContext<'input> + 'input > >, invoking_state: isize) -> Rc<StructDeclContextAll<'input>> {
		Rc::new(
			BaseParserRuleContext::new_parser_ctx(parent, invoking_state,StructDeclContextExt{
				annotation: None, typeName: None, targetType: None, typeConstraints: None, structDefDecl: None, 
				annotations: Vec::new(), decls: Vec::new(), 
				ph:PhantomData
			}),
		)
	}
}

pub trait StructDeclContextAttrs<'input>: LibSLParserContext<'input> + BorrowMut<StructDeclContextExt<'input>>{

/// Retrieves first TerminalNode corresponding to token TYPE
/// Returns `None` if there is no child corresponding to token TYPE
fn TYPE(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(TYPE, 0)
}
fn qualifiedTypeName(&self) -> Option<Rc<QualifiedTypeNameContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}
/// Retrieves first TerminalNode corresponding to token L_BRACE
/// Returns `None` if there is no child corresponding to token L_BRACE
fn L_BRACE(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(L_BRACE, 0)
}
/// Retrieves first TerminalNode corresponding to token R_BRACE
/// Returns `None` if there is no child corresponding to token R_BRACE
fn R_BRACE(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(R_BRACE, 0)
}
fn annotation_all(&self) ->  Vec<Rc<AnnotationContextAll<'input>>> where Self:Sized{
	self.children_of_type()
}
fn annotation(&self, i: usize) -> Option<Rc<AnnotationContextAll<'input>>> where Self:Sized{
	self.child_of_type(i)
}
fn structTargetType(&self) -> Option<Rc<StructTargetTypeContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}
fn whereClause(&self) -> Option<Rc<WhereClauseContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}
fn structDefDecl_all(&self) ->  Vec<Rc<StructDefDeclContextAll<'input>>> where Self:Sized{
	self.children_of_type()
}
fn structDefDecl(&self, i: usize) -> Option<Rc<StructDefDeclContextAll<'input>>> where Self:Sized{
	self.child_of_type(i)
}

}

impl<'input> StructDeclContextAttrs<'input> for StructDeclContext<'input>{}

impl<'input, I, H> LibSLParser<'input, I, H>
where
    I: TokenStream<'input, TF = LocalTokenFactory<'input> > + TidAble<'input>,
    H: ErrorStrategy<'input,BaseParserType<'input,I>>
{
	pub fn structDecl(&mut self,)
	-> Result<Rc<StructDeclContextAll<'input>>,ANTLRError> {
		let mut recog = self;
		let _parentctx = recog.ctx.take();
		let mut _localctx = StructDeclContextExt::new(_parentctx.clone(), recog.base.get_state());
        recog.base.enter_rule(_localctx.clone(), 22, RULE_structDecl);
        let mut _localctx: Rc<StructDeclContextAll> = _localctx;
		let mut _la: isize = -1;
		let result: Result<(), ANTLRError> = (|| {

			//recog.base.enter_outer_alt(_localctx.clone(), 1);
			recog.base.enter_outer_alt(None, 1);
			{
			recog.base.set_state(316);
			recog.err_handler.sync(&mut recog.base)?;
			_la = recog.base.input.la(1);
			while _la==AT {
				{
				{
				/*InvokeRule annotation*/
				recog.base.set_state(313);
				let tmp = recog.annotation()?;
				 cast_mut::<_,StructDeclContext >(&mut _localctx).annotation = Some(tmp.clone());
				  

				let temp =  cast_mut::<_,StructDeclContext >(&mut _localctx).annotation.clone().unwrap()
				 ;
				 cast_mut::<_,StructDeclContext >(&mut _localctx).annotations.push(temp);
				  
				}
				}
				recog.base.set_state(318);
				recog.err_handler.sync(&mut recog.base)?;
				_la = recog.base.input.la(1);
			}
			recog.base.set_state(319);
			recog.base.match_token(TYPE,&mut recog.err_handler)?;

			/*InvokeRule qualifiedTypeName*/
			recog.base.set_state(320);
			let tmp = recog.qualifiedTypeName()?;
			 cast_mut::<_,StructDeclContext >(&mut _localctx).typeName = Some(tmp.clone());
			  

			recog.base.set_state(322);
			recog.err_handler.sync(&mut recog.base)?;
			_la = recog.base.input.la(1);
			if _la==IS || _la==FOR {
				{
				/*InvokeRule structTargetType*/
				recog.base.set_state(321);
				let tmp = recog.structTargetType()?;
				 cast_mut::<_,StructDeclContext >(&mut _localctx).targetType = Some(tmp.clone());
				  

				}
			}

			recog.base.set_state(325);
			recog.err_handler.sync(&mut recog.base)?;
			_la = recog.base.input.la(1);
			if _la==WHERE {
				{
				/*InvokeRule whereClause*/
				recog.base.set_state(324);
				let tmp = recog.whereClause()?;
				 cast_mut::<_,StructDeclContext >(&mut _localctx).typeConstraints = Some(tmp.clone());
				  

				}
			}

			recog.base.set_state(335);
			recog.err_handler.sync(&mut recog.base)?;
			_la = recog.base.input.la(1);
			if _la==L_BRACE {
				{
				recog.base.set_state(327);
				recog.base.match_token(L_BRACE,&mut recog.err_handler)?;

				recog.base.set_state(331);
				recog.err_handler.sync(&mut recog.base)?;
				_la = recog.base.input.la(1);
				while ((((_la - 57)) & !0x3f) == 0 && ((1usize << (_la - 57)) & 3221228675) != 0) || _la==AT {
					{
					{
					/*InvokeRule structDefDecl*/
					recog.base.set_state(328);
					let tmp = recog.structDefDecl()?;
					 cast_mut::<_,StructDeclContext >(&mut _localctx).structDefDecl = Some(tmp.clone());
					  

					let temp =  cast_mut::<_,StructDeclContext >(&mut _localctx).structDefDecl.clone().unwrap()
					 ;
					 cast_mut::<_,StructDeclContext >(&mut _localctx).decls.push(temp);
					  
					}
					}
					recog.base.set_state(333);
					recog.err_handler.sync(&mut recog.base)?;
					_la = recog.base.input.la(1);
				}
				recog.base.set_state(334);
				recog.base.match_token(R_BRACE,&mut recog.err_handler)?;

				}
			}

			}
			Ok(())
		})();
		match result {
		Ok(_)=>{},
        Err(e @ ANTLRError::FallThrough(_)) => return Err(e),
		Err(ref re) => {
				//_localctx.exception = re;
				recog.err_handler.report_error(&mut recog.base, re);
				recog.err_handler.recover(&mut recog.base, re)?;
			}
		}
		recog.base.exit_rule();

		Ok(_localctx)
	}
}
//------------------- structTargetType ----------------
pub type StructTargetTypeContextAll<'input> = StructTargetTypeContext<'input>;


pub type StructTargetTypeContext<'input> = BaseParserRuleContext<'input,StructTargetTypeContextExt<'input>>;

#[derive(Clone)]
pub struct StructTargetTypeContextExt<'input>{
	pub isType: Option<Rc<TypeExprContextAll<'input>>>,
	pub forTypes: Option<Rc<TypeExprListContextAll<'input>>>,
ph:PhantomData<&'input str>
}

impl<'input> LibSLParserContext<'input> for StructTargetTypeContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for StructTargetTypeContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_structTargetType(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_structTargetType(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for StructTargetTypeContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_structTargetType }
	//fn type_rule_index() -> usize where Self: Sized { RULE_structTargetType }
}
antlr_rust::tid!{StructTargetTypeContextExt<'a>}

impl<'input> StructTargetTypeContextExt<'input>{
	fn new(parent: Option<Rc<dyn LibSLParserContext<'input> + 'input > >, invoking_state: isize) -> Rc<StructTargetTypeContextAll<'input>> {
		Rc::new(
			BaseParserRuleContext::new_parser_ctx(parent, invoking_state,StructTargetTypeContextExt{
				isType: None, forTypes: None, 
				ph:PhantomData
			}),
		)
	}
}

pub trait StructTargetTypeContextAttrs<'input>: LibSLParserContext<'input> + BorrowMut<StructTargetTypeContextExt<'input>>{

/// Retrieves first TerminalNode corresponding to token FOR
/// Returns `None` if there is no child corresponding to token FOR
fn FOR(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(FOR, 0)
}
fn typeExprList(&self) -> Option<Rc<TypeExprListContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}
/// Retrieves first TerminalNode corresponding to token IS
/// Returns `None` if there is no child corresponding to token IS
fn IS(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(IS, 0)
}
/// Retrieves first TerminalNode corresponding to token COMMA
/// Returns `None` if there is no child corresponding to token COMMA
fn COMMA(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(COMMA, 0)
}
fn typeExpr(&self) -> Option<Rc<TypeExprContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}

}

impl<'input> StructTargetTypeContextAttrs<'input> for StructTargetTypeContext<'input>{}

impl<'input, I, H> LibSLParser<'input, I, H>
where
    I: TokenStream<'input, TF = LocalTokenFactory<'input> > + TidAble<'input>,
    H: ErrorStrategy<'input,BaseParserType<'input,I>>
{
	pub fn structTargetType(&mut self,)
	-> Result<Rc<StructTargetTypeContextAll<'input>>,ANTLRError> {
		let mut recog = self;
		let _parentctx = recog.ctx.take();
		let mut _localctx = StructTargetTypeContextExt::new(_parentctx.clone(), recog.base.get_state());
        recog.base.enter_rule(_localctx.clone(), 24, RULE_structTargetType);
        let mut _localctx: Rc<StructTargetTypeContextAll> = _localctx;
		let mut _la: isize = -1;
		let result: Result<(), ANTLRError> = (|| {

			//recog.base.enter_outer_alt(_localctx.clone(), 1);
			recog.base.enter_outer_alt(None, 1);
			{
			recog.base.set_state(339);
			recog.err_handler.sync(&mut recog.base)?;
			_la = recog.base.input.la(1);
			if _la==IS {
				{
				recog.base.set_state(337);
				recog.base.match_token(IS,&mut recog.err_handler)?;

				/*InvokeRule typeExpr*/
				recog.base.set_state(338);
				let tmp = recog.typeExpr_rec(0)?;
				 cast_mut::<_,StructTargetTypeContext >(&mut _localctx).isType = Some(tmp.clone());
				  

				}
			}

			recog.base.set_state(341);
			recog.base.match_token(FOR,&mut recog.err_handler)?;

			/*InvokeRule typeExprList*/
			recog.base.set_state(342);
			let tmp = recog.typeExprList()?;
			 cast_mut::<_,StructTargetTypeContext >(&mut _localctx).forTypes = Some(tmp.clone());
			  

			recog.base.set_state(344);
			recog.err_handler.sync(&mut recog.base)?;
			_la = recog.base.input.la(1);
			if _la==COMMA {
				{
				recog.base.set_state(343);
				recog.base.match_token(COMMA,&mut recog.err_handler)?;

				}
			}

			}
			Ok(())
		})();
		match result {
		Ok(_)=>{},
        Err(e @ ANTLRError::FallThrough(_)) => return Err(e),
		Err(ref re) => {
				//_localctx.exception = re;
				recog.err_handler.report_error(&mut recog.base, re);
				recog.err_handler.recover(&mut recog.base, re)?;
			}
		}
		recog.base.exit_rule();

		Ok(_localctx)
	}
}
//------------------- structDefDecl ----------------
#[derive(Debug)]
pub enum StructDefDeclContextAll<'input>{
	StructDefDeclProcContext(StructDefDeclProcContext<'input>),
	StructDefDeclVariableContext(StructDefDeclVariableContext<'input>),
	StructDefDeclPredContext(StructDefDeclPredContext<'input>),
	StructDefDeclFunctionContext(StructDefDeclFunctionContext<'input>),
Error(StructDefDeclContext<'input>)
}
antlr_rust::tid!{StructDefDeclContextAll<'a>}

impl<'input> antlr_rust::parser_rule_context::DerefSeal for StructDefDeclContextAll<'input>{}

impl<'input> LibSLParserContext<'input> for StructDefDeclContextAll<'input>{}

impl<'input> Deref for StructDefDeclContextAll<'input>{
	type Target = dyn StructDefDeclContextAttrs<'input> + 'input;
	fn deref(&self) -> &Self::Target{
		use StructDefDeclContextAll::*;
		match self{
			StructDefDeclProcContext(inner) => inner,
			StructDefDeclVariableContext(inner) => inner,
			StructDefDeclPredContext(inner) => inner,
			StructDefDeclFunctionContext(inner) => inner,
Error(inner) => inner
		}
	}
}
impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for StructDefDeclContextAll<'input>{
    fn enter(&self, listener: &mut (dyn LibSLParserListener<'input> + 'a)) { self.deref().enter(listener) }
    fn exit(&self, listener: &mut (dyn LibSLParserListener<'input> + 'a)) { self.deref().exit(listener) }
}



pub type StructDefDeclContext<'input> = BaseParserRuleContext<'input,StructDefDeclContextExt<'input>>;

#[derive(Clone)]
pub struct StructDefDeclContextExt<'input>{
ph:PhantomData<&'input str>
}

impl<'input> LibSLParserContext<'input> for StructDefDeclContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for StructDefDeclContext<'input>{
}

impl<'input> CustomRuleContext<'input> for StructDefDeclContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_structDefDecl }
	//fn type_rule_index() -> usize where Self: Sized { RULE_structDefDecl }
}
antlr_rust::tid!{StructDefDeclContextExt<'a>}

impl<'input> StructDefDeclContextExt<'input>{
	fn new(parent: Option<Rc<dyn LibSLParserContext<'input> + 'input > >, invoking_state: isize) -> Rc<StructDefDeclContextAll<'input>> {
		Rc::new(
		StructDefDeclContextAll::Error(
			BaseParserRuleContext::new_parser_ctx(parent, invoking_state,StructDefDeclContextExt{
				ph:PhantomData
			}),
		)
		)
	}
}

pub trait StructDefDeclContextAttrs<'input>: LibSLParserContext<'input> + BorrowMut<StructDefDeclContextExt<'input>>{


}

impl<'input> StructDefDeclContextAttrs<'input> for StructDefDeclContext<'input>{}

pub type StructDefDeclProcContext<'input> = BaseParserRuleContext<'input,StructDefDeclProcContextExt<'input>>;

pub trait StructDefDeclProcContextAttrs<'input>: LibSLParserContext<'input>{
	fn procDecl(&self) -> Option<Rc<ProcDeclContextAll<'input>>> where Self:Sized{
		self.child_of_type(0)
	}
}

impl<'input> StructDefDeclProcContextAttrs<'input> for StructDefDeclProcContext<'input>{}

pub struct StructDefDeclProcContextExt<'input>{
	__base:StructDefDeclContextExt<'input>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{StructDefDeclProcContextExt<'a>}

impl<'input> LibSLParserContext<'input> for StructDefDeclProcContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for StructDefDeclProcContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_StructDefDeclProc(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_StructDefDeclProc(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for StructDefDeclProcContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_structDefDecl }
	//fn type_rule_index() -> usize where Self: Sized { RULE_structDefDecl }
}

impl<'input> Borrow<StructDefDeclContextExt<'input>> for StructDefDeclProcContext<'input>{
	fn borrow(&self) -> &StructDefDeclContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<StructDefDeclContextExt<'input>> for StructDefDeclProcContext<'input>{
	fn borrow_mut(&mut self) -> &mut StructDefDeclContextExt<'input> { &mut self.__base }
}

impl<'input> StructDefDeclContextAttrs<'input> for StructDefDeclProcContext<'input> {}

impl<'input> StructDefDeclProcContextExt<'input>{
	fn new(ctx: &dyn StructDefDeclContextAttrs<'input>) -> Rc<StructDefDeclContextAll<'input>>  {
		Rc::new(
			StructDefDeclContextAll::StructDefDeclProcContext(
				BaseParserRuleContext::copy_from(ctx,StructDefDeclProcContextExt{
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type StructDefDeclVariableContext<'input> = BaseParserRuleContext<'input,StructDefDeclVariableContextExt<'input>>;

pub trait StructDefDeclVariableContextAttrs<'input>: LibSLParserContext<'input>{
	fn variableDecl(&self) -> Option<Rc<VariableDeclContextAll<'input>>> where Self:Sized{
		self.child_of_type(0)
	}
}

impl<'input> StructDefDeclVariableContextAttrs<'input> for StructDefDeclVariableContext<'input>{}

pub struct StructDefDeclVariableContextExt<'input>{
	__base:StructDefDeclContextExt<'input>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{StructDefDeclVariableContextExt<'a>}

impl<'input> LibSLParserContext<'input> for StructDefDeclVariableContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for StructDefDeclVariableContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_StructDefDeclVariable(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_StructDefDeclVariable(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for StructDefDeclVariableContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_structDefDecl }
	//fn type_rule_index() -> usize where Self: Sized { RULE_structDefDecl }
}

impl<'input> Borrow<StructDefDeclContextExt<'input>> for StructDefDeclVariableContext<'input>{
	fn borrow(&self) -> &StructDefDeclContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<StructDefDeclContextExt<'input>> for StructDefDeclVariableContext<'input>{
	fn borrow_mut(&mut self) -> &mut StructDefDeclContextExt<'input> { &mut self.__base }
}

impl<'input> StructDefDeclContextAttrs<'input> for StructDefDeclVariableContext<'input> {}

impl<'input> StructDefDeclVariableContextExt<'input>{
	fn new(ctx: &dyn StructDefDeclContextAttrs<'input>) -> Rc<StructDefDeclContextAll<'input>>  {
		Rc::new(
			StructDefDeclContextAll::StructDefDeclVariableContext(
				BaseParserRuleContext::copy_from(ctx,StructDefDeclVariableContextExt{
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type StructDefDeclPredContext<'input> = BaseParserRuleContext<'input,StructDefDeclPredContextExt<'input>>;

pub trait StructDefDeclPredContextAttrs<'input>: LibSLParserContext<'input>{
	fn predDecl(&self) -> Option<Rc<PredDeclContextAll<'input>>> where Self:Sized{
		self.child_of_type(0)
	}
}

impl<'input> StructDefDeclPredContextAttrs<'input> for StructDefDeclPredContext<'input>{}

pub struct StructDefDeclPredContextExt<'input>{
	__base:StructDefDeclContextExt<'input>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{StructDefDeclPredContextExt<'a>}

impl<'input> LibSLParserContext<'input> for StructDefDeclPredContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for StructDefDeclPredContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_StructDefDeclPred(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_StructDefDeclPred(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for StructDefDeclPredContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_structDefDecl }
	//fn type_rule_index() -> usize where Self: Sized { RULE_structDefDecl }
}

impl<'input> Borrow<StructDefDeclContextExt<'input>> for StructDefDeclPredContext<'input>{
	fn borrow(&self) -> &StructDefDeclContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<StructDefDeclContextExt<'input>> for StructDefDeclPredContext<'input>{
	fn borrow_mut(&mut self) -> &mut StructDefDeclContextExt<'input> { &mut self.__base }
}

impl<'input> StructDefDeclContextAttrs<'input> for StructDefDeclPredContext<'input> {}

impl<'input> StructDefDeclPredContextExt<'input>{
	fn new(ctx: &dyn StructDefDeclContextAttrs<'input>) -> Rc<StructDefDeclContextAll<'input>>  {
		Rc::new(
			StructDefDeclContextAll::StructDefDeclPredContext(
				BaseParserRuleContext::copy_from(ctx,StructDefDeclPredContextExt{
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type StructDefDeclFunctionContext<'input> = BaseParserRuleContext<'input,StructDefDeclFunctionContextExt<'input>>;

pub trait StructDefDeclFunctionContextAttrs<'input>: LibSLParserContext<'input>{
	fn functionDecl(&self) -> Option<Rc<FunctionDeclContextAll<'input>>> where Self:Sized{
		self.child_of_type(0)
	}
}

impl<'input> StructDefDeclFunctionContextAttrs<'input> for StructDefDeclFunctionContext<'input>{}

pub struct StructDefDeclFunctionContextExt<'input>{
	__base:StructDefDeclContextExt<'input>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{StructDefDeclFunctionContextExt<'a>}

impl<'input> LibSLParserContext<'input> for StructDefDeclFunctionContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for StructDefDeclFunctionContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_StructDefDeclFunction(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_StructDefDeclFunction(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for StructDefDeclFunctionContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_structDefDecl }
	//fn type_rule_index() -> usize where Self: Sized { RULE_structDefDecl }
}

impl<'input> Borrow<StructDefDeclContextExt<'input>> for StructDefDeclFunctionContext<'input>{
	fn borrow(&self) -> &StructDefDeclContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<StructDefDeclContextExt<'input>> for StructDefDeclFunctionContext<'input>{
	fn borrow_mut(&mut self) -> &mut StructDefDeclContextExt<'input> { &mut self.__base }
}

impl<'input> StructDefDeclContextAttrs<'input> for StructDefDeclFunctionContext<'input> {}

impl<'input> StructDefDeclFunctionContextExt<'input>{
	fn new(ctx: &dyn StructDefDeclContextAttrs<'input>) -> Rc<StructDefDeclContextAll<'input>>  {
		Rc::new(
			StructDefDeclContextAll::StructDefDeclFunctionContext(
				BaseParserRuleContext::copy_from(ctx,StructDefDeclFunctionContextExt{
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

impl<'input, I, H> LibSLParser<'input, I, H>
where
    I: TokenStream<'input, TF = LocalTokenFactory<'input> > + TidAble<'input>,
    H: ErrorStrategy<'input,BaseParserType<'input,I>>
{
	pub fn structDefDecl(&mut self,)
	-> Result<Rc<StructDefDeclContextAll<'input>>,ANTLRError> {
		let mut recog = self;
		let _parentctx = recog.ctx.take();
		let mut _localctx = StructDefDeclContextExt::new(_parentctx.clone(), recog.base.get_state());
        recog.base.enter_rule(_localctx.clone(), 26, RULE_structDefDecl);
        let mut _localctx: Rc<StructDefDeclContextAll> = _localctx;
		let result: Result<(), ANTLRError> = (|| {

			recog.base.set_state(350);
			recog.err_handler.sync(&mut recog.base)?;
			match  recog.interpreter.adaptive_predict(19,&mut recog.base)? {
				1 =>{
					let tmp = StructDefDeclVariableContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 1);
					_localctx = tmp;
					{
					/*InvokeRule variableDecl*/
					recog.base.set_state(346);
					recog.variableDecl()?;

					}
				}
			,
				2 =>{
					let tmp = StructDefDeclFunctionContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 2);
					_localctx = tmp;
					{
					/*InvokeRule functionDecl*/
					recog.base.set_state(347);
					recog.functionDecl()?;

					}
				}
			,
				3 =>{
					let tmp = StructDefDeclProcContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 3);
					_localctx = tmp;
					{
					/*InvokeRule procDecl*/
					recog.base.set_state(348);
					recog.procDecl()?;

					}
				}
			,
				4 =>{
					let tmp = StructDefDeclPredContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 4);
					_localctx = tmp;
					{
					/*InvokeRule predDecl*/
					recog.base.set_state(349);
					recog.predDecl()?;

					}
				}

				_ => {}
			}
			Ok(())
		})();
		match result {
		Ok(_)=>{},
        Err(e @ ANTLRError::FallThrough(_)) => return Err(e),
		Err(ref re) => {
				//_localctx.exception = re;
				recog.err_handler.report_error(&mut recog.base, re);
				recog.err_handler.recover(&mut recog.base, re)?;
			}
		}
		recog.base.exit_rule();

		Ok(_localctx)
	}
}
//------------------- enumDecl ----------------
pub type EnumDeclContextAll<'input> = EnumDeclContext<'input>;


pub type EnumDeclContext<'input> = BaseParserRuleContext<'input,EnumDeclContextExt<'input>>;

#[derive(Clone)]
pub struct EnumDeclContextExt<'input>{
	pub annotation: Option<Rc<AnnotationContextAll<'input>>>,
	pub annotations:Vec<Rc<AnnotationContextAll<'input>>>,
	pub typeName: Option<Rc<QualifiedTypeNameContextAll<'input>>>,
	pub enumDeclVariant: Option<Rc<EnumDeclVariantContextAll<'input>>>,
	pub variants:Vec<Rc<EnumDeclVariantContextAll<'input>>>,
ph:PhantomData<&'input str>
}

impl<'input> LibSLParserContext<'input> for EnumDeclContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for EnumDeclContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_enumDecl(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_enumDecl(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for EnumDeclContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_enumDecl }
	//fn type_rule_index() -> usize where Self: Sized { RULE_enumDecl }
}
antlr_rust::tid!{EnumDeclContextExt<'a>}

impl<'input> EnumDeclContextExt<'input>{
	fn new(parent: Option<Rc<dyn LibSLParserContext<'input> + 'input > >, invoking_state: isize) -> Rc<EnumDeclContextAll<'input>> {
		Rc::new(
			BaseParserRuleContext::new_parser_ctx(parent, invoking_state,EnumDeclContextExt{
				annotation: None, typeName: None, enumDeclVariant: None, 
				annotations: Vec::new(), variants: Vec::new(), 
				ph:PhantomData
			}),
		)
	}
}

pub trait EnumDeclContextAttrs<'input>: LibSLParserContext<'input> + BorrowMut<EnumDeclContextExt<'input>>{

/// Retrieves first TerminalNode corresponding to token ENUM
/// Returns `None` if there is no child corresponding to token ENUM
fn ENUM(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(ENUM, 0)
}
/// Retrieves first TerminalNode corresponding to token L_BRACE
/// Returns `None` if there is no child corresponding to token L_BRACE
fn L_BRACE(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(L_BRACE, 0)
}
/// Retrieves first TerminalNode corresponding to token R_BRACE
/// Returns `None` if there is no child corresponding to token R_BRACE
fn R_BRACE(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(R_BRACE, 0)
}
fn qualifiedTypeName(&self) -> Option<Rc<QualifiedTypeNameContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}
fn annotation_all(&self) ->  Vec<Rc<AnnotationContextAll<'input>>> where Self:Sized{
	self.children_of_type()
}
fn annotation(&self, i: usize) -> Option<Rc<AnnotationContextAll<'input>>> where Self:Sized{
	self.child_of_type(i)
}
fn enumDeclVariant_all(&self) ->  Vec<Rc<EnumDeclVariantContextAll<'input>>> where Self:Sized{
	self.children_of_type()
}
fn enumDeclVariant(&self, i: usize) -> Option<Rc<EnumDeclVariantContextAll<'input>>> where Self:Sized{
	self.child_of_type(i)
}

}

impl<'input> EnumDeclContextAttrs<'input> for EnumDeclContext<'input>{}

impl<'input, I, H> LibSLParser<'input, I, H>
where
    I: TokenStream<'input, TF = LocalTokenFactory<'input> > + TidAble<'input>,
    H: ErrorStrategy<'input,BaseParserType<'input,I>>
{
	pub fn enumDecl(&mut self,)
	-> Result<Rc<EnumDeclContextAll<'input>>,ANTLRError> {
		let mut recog = self;
		let _parentctx = recog.ctx.take();
		let mut _localctx = EnumDeclContextExt::new(_parentctx.clone(), recog.base.get_state());
        recog.base.enter_rule(_localctx.clone(), 28, RULE_enumDecl);
        let mut _localctx: Rc<EnumDeclContextAll> = _localctx;
		let mut _la: isize = -1;
		let result: Result<(), ANTLRError> = (|| {

			//recog.base.enter_outer_alt(_localctx.clone(), 1);
			recog.base.enter_outer_alt(None, 1);
			{
			recog.base.set_state(355);
			recog.err_handler.sync(&mut recog.base)?;
			_la = recog.base.input.la(1);
			while _la==AT {
				{
				{
				/*InvokeRule annotation*/
				recog.base.set_state(352);
				let tmp = recog.annotation()?;
				 cast_mut::<_,EnumDeclContext >(&mut _localctx).annotation = Some(tmp.clone());
				  

				let temp =  cast_mut::<_,EnumDeclContext >(&mut _localctx).annotation.clone().unwrap()
				 ;
				 cast_mut::<_,EnumDeclContext >(&mut _localctx).annotations.push(temp);
				  
				}
				}
				recog.base.set_state(357);
				recog.err_handler.sync(&mut recog.base)?;
				_la = recog.base.input.la(1);
			}
			recog.base.set_state(358);
			recog.base.match_token(ENUM,&mut recog.err_handler)?;

			/*InvokeRule qualifiedTypeName*/
			recog.base.set_state(359);
			let tmp = recog.qualifiedTypeName()?;
			 cast_mut::<_,EnumDeclContext >(&mut _localctx).typeName = Some(tmp.clone());
			  

			recog.base.set_state(360);
			recog.base.match_token(L_BRACE,&mut recog.err_handler)?;

			recog.base.set_state(364);
			recog.err_handler.sync(&mut recog.base)?;
			_la = recog.base.input.la(1);
			while ((((_la - 86)) & !0x3f) == 0 && ((1usize << (_la - 86)) & 519) != 0) {
				{
				{
				/*InvokeRule enumDeclVariant*/
				recog.base.set_state(361);
				let tmp = recog.enumDeclVariant()?;
				 cast_mut::<_,EnumDeclContext >(&mut _localctx).enumDeclVariant = Some(tmp.clone());
				  

				let temp =  cast_mut::<_,EnumDeclContext >(&mut _localctx).enumDeclVariant.clone().unwrap()
				 ;
				 cast_mut::<_,EnumDeclContext >(&mut _localctx).variants.push(temp);
				  
				}
				}
				recog.base.set_state(366);
				recog.err_handler.sync(&mut recog.base)?;
				_la = recog.base.input.la(1);
			}
			recog.base.set_state(367);
			recog.base.match_token(R_BRACE,&mut recog.err_handler)?;

			}
			Ok(())
		})();
		match result {
		Ok(_)=>{},
        Err(e @ ANTLRError::FallThrough(_)) => return Err(e),
		Err(ref re) => {
				//_localctx.exception = re;
				recog.err_handler.report_error(&mut recog.base, re);
				recog.err_handler.recover(&mut recog.base, re)?;
			}
		}
		recog.base.exit_rule();

		Ok(_localctx)
	}
}
//------------------- enumDeclVariant ----------------
pub type EnumDeclVariantContextAll<'input> = EnumDeclVariantContext<'input>;


pub type EnumDeclVariantContext<'input> = BaseParserRuleContext<'input,EnumDeclVariantContextExt<'input>>;

#[derive(Clone)]
pub struct EnumDeclVariantContextExt<'input>{
	pub name: Option<Rc<IdentContextAll<'input>>>,
	pub value: Option<Rc<SignedIntLitContextAll<'input>>>,
ph:PhantomData<&'input str>
}

impl<'input> LibSLParserContext<'input> for EnumDeclVariantContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for EnumDeclVariantContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_enumDeclVariant(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_enumDeclVariant(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for EnumDeclVariantContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_enumDeclVariant }
	//fn type_rule_index() -> usize where Self: Sized { RULE_enumDeclVariant }
}
antlr_rust::tid!{EnumDeclVariantContextExt<'a>}

impl<'input> EnumDeclVariantContextExt<'input>{
	fn new(parent: Option<Rc<dyn LibSLParserContext<'input> + 'input > >, invoking_state: isize) -> Rc<EnumDeclVariantContextAll<'input>> {
		Rc::new(
			BaseParserRuleContext::new_parser_ctx(parent, invoking_state,EnumDeclVariantContextExt{
				name: None, value: None, 
				ph:PhantomData
			}),
		)
	}
}

pub trait EnumDeclVariantContextAttrs<'input>: LibSLParserContext<'input> + BorrowMut<EnumDeclVariantContextExt<'input>>{

/// Retrieves first TerminalNode corresponding to token EQ
/// Returns `None` if there is no child corresponding to token EQ
fn EQ(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(EQ, 0)
}
/// Retrieves first TerminalNode corresponding to token SEMICOLON
/// Returns `None` if there is no child corresponding to token SEMICOLON
fn SEMICOLON(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(SEMICOLON, 0)
}
fn ident(&self) -> Option<Rc<IdentContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}
fn signedIntLit(&self) -> Option<Rc<SignedIntLitContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}

}

impl<'input> EnumDeclVariantContextAttrs<'input> for EnumDeclVariantContext<'input>{}

impl<'input, I, H> LibSLParser<'input, I, H>
where
    I: TokenStream<'input, TF = LocalTokenFactory<'input> > + TidAble<'input>,
    H: ErrorStrategy<'input,BaseParserType<'input,I>>
{
	pub fn enumDeclVariant(&mut self,)
	-> Result<Rc<EnumDeclVariantContextAll<'input>>,ANTLRError> {
		let mut recog = self;
		let _parentctx = recog.ctx.take();
		let mut _localctx = EnumDeclVariantContextExt::new(_parentctx.clone(), recog.base.get_state());
        recog.base.enter_rule(_localctx.clone(), 30, RULE_enumDeclVariant);
        let mut _localctx: Rc<EnumDeclVariantContextAll> = _localctx;
		let result: Result<(), ANTLRError> = (|| {

			//recog.base.enter_outer_alt(_localctx.clone(), 1);
			recog.base.enter_outer_alt(None, 1);
			{
			/*InvokeRule ident*/
			recog.base.set_state(369);
			let tmp = recog.ident()?;
			 cast_mut::<_,EnumDeclVariantContext >(&mut _localctx).name = Some(tmp.clone());
			  

			recog.base.set_state(370);
			recog.base.match_token(EQ,&mut recog.err_handler)?;

			/*InvokeRule signedIntLit*/
			recog.base.set_state(371);
			let tmp = recog.signedIntLit()?;
			 cast_mut::<_,EnumDeclVariantContext >(&mut _localctx).value = Some(tmp.clone());
			  

			recog.base.set_state(372);
			recog.base.match_token(SEMICOLON,&mut recog.err_handler)?;

			}
			Ok(())
		})();
		match result {
		Ok(_)=>{},
        Err(e @ ANTLRError::FallThrough(_)) => return Err(e),
		Err(ref re) => {
				//_localctx.exception = re;
				recog.err_handler.report_error(&mut recog.base, re);
				recog.err_handler.recover(&mut recog.base, re)?;
			}
		}
		recog.base.exit_rule();

		Ok(_localctx)
	}
}
//------------------- signedIntLit ----------------
pub type SignedIntLitContextAll<'input> = SignedIntLitContext<'input>;


pub type SignedIntLitContext<'input> = BaseParserRuleContext<'input,SignedIntLitContextExt<'input>>;

#[derive(Clone)]
pub struct SignedIntLitContextExt<'input>{
	pub lit: Option<TokenType<'input>>,
ph:PhantomData<&'input str>
}

impl<'input> LibSLParserContext<'input> for SignedIntLitContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for SignedIntLitContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_signedIntLit(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_signedIntLit(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for SignedIntLitContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_signedIntLit }
	//fn type_rule_index() -> usize where Self: Sized { RULE_signedIntLit }
}
antlr_rust::tid!{SignedIntLitContextExt<'a>}

impl<'input> SignedIntLitContextExt<'input>{
	fn new(parent: Option<Rc<dyn LibSLParserContext<'input> + 'input > >, invoking_state: isize) -> Rc<SignedIntLitContextAll<'input>> {
		Rc::new(
			BaseParserRuleContext::new_parser_ctx(parent, invoking_state,SignedIntLitContextExt{
				lit: None, 
				ph:PhantomData
			}),
		)
	}
}

pub trait SignedIntLitContextAttrs<'input>: LibSLParserContext<'input> + BorrowMut<SignedIntLitContextExt<'input>>{

/// Retrieves first TerminalNode corresponding to token IntegerLit
/// Returns `None` if there is no child corresponding to token IntegerLit
fn IntegerLit(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(IntegerLit, 0)
}
fn sign(&self) -> Option<Rc<SignContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}

}

impl<'input> SignedIntLitContextAttrs<'input> for SignedIntLitContext<'input>{}

impl<'input, I, H> LibSLParser<'input, I, H>
where
    I: TokenStream<'input, TF = LocalTokenFactory<'input> > + TidAble<'input>,
    H: ErrorStrategy<'input,BaseParserType<'input,I>>
{
	pub fn signedIntLit(&mut self,)
	-> Result<Rc<SignedIntLitContextAll<'input>>,ANTLRError> {
		let mut recog = self;
		let _parentctx = recog.ctx.take();
		let mut _localctx = SignedIntLitContextExt::new(_parentctx.clone(), recog.base.get_state());
        recog.base.enter_rule(_localctx.clone(), 32, RULE_signedIntLit);
        let mut _localctx: Rc<SignedIntLitContextAll> = _localctx;
		let mut _la: isize = -1;
		let result: Result<(), ANTLRError> = (|| {

			//recog.base.enter_outer_alt(_localctx.clone(), 1);
			recog.base.enter_outer_alt(None, 1);
			{
			recog.base.set_state(375);
			recog.err_handler.sync(&mut recog.base)?;
			_la = recog.base.input.la(1);
			if _la==PLUS || _la==MINUS {
				{
				/*InvokeRule sign*/
				recog.base.set_state(374);
				recog.sign()?;

				}
			}

			recog.base.set_state(377);
			let tmp = recog.base.match_token(IntegerLit,&mut recog.err_handler)?;
			 cast_mut::<_,SignedIntLitContext >(&mut _localctx).lit = Some(tmp.clone());
			  

			}
			Ok(())
		})();
		match result {
		Ok(_)=>{},
        Err(e @ ANTLRError::FallThrough(_)) => return Err(e),
		Err(ref re) => {
				//_localctx.exception = re;
				recog.err_handler.report_error(&mut recog.base, re);
				recog.err_handler.recover(&mut recog.base, re)?;
			}
		}
		recog.base.exit_rule();

		Ok(_localctx)
	}
}
//------------------- sign ----------------
#[derive(Debug)]
pub enum SignContextAll<'input>{
	PlusSignContext(PlusSignContext<'input>),
	MinusSignContext(MinusSignContext<'input>),
Error(SignContext<'input>)
}
antlr_rust::tid!{SignContextAll<'a>}

impl<'input> antlr_rust::parser_rule_context::DerefSeal for SignContextAll<'input>{}

impl<'input> LibSLParserContext<'input> for SignContextAll<'input>{}

impl<'input> Deref for SignContextAll<'input>{
	type Target = dyn SignContextAttrs<'input> + 'input;
	fn deref(&self) -> &Self::Target{
		use SignContextAll::*;
		match self{
			PlusSignContext(inner) => inner,
			MinusSignContext(inner) => inner,
Error(inner) => inner
		}
	}
}
impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for SignContextAll<'input>{
    fn enter(&self, listener: &mut (dyn LibSLParserListener<'input> + 'a)) { self.deref().enter(listener) }
    fn exit(&self, listener: &mut (dyn LibSLParserListener<'input> + 'a)) { self.deref().exit(listener) }
}



pub type SignContext<'input> = BaseParserRuleContext<'input,SignContextExt<'input>>;

#[derive(Clone)]
pub struct SignContextExt<'input>{
ph:PhantomData<&'input str>
}

impl<'input> LibSLParserContext<'input> for SignContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for SignContext<'input>{
}

impl<'input> CustomRuleContext<'input> for SignContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_sign }
	//fn type_rule_index() -> usize where Self: Sized { RULE_sign }
}
antlr_rust::tid!{SignContextExt<'a>}

impl<'input> SignContextExt<'input>{
	fn new(parent: Option<Rc<dyn LibSLParserContext<'input> + 'input > >, invoking_state: isize) -> Rc<SignContextAll<'input>> {
		Rc::new(
		SignContextAll::Error(
			BaseParserRuleContext::new_parser_ctx(parent, invoking_state,SignContextExt{
				ph:PhantomData
			}),
		)
		)
	}
}

pub trait SignContextAttrs<'input>: LibSLParserContext<'input> + BorrowMut<SignContextExt<'input>>{


}

impl<'input> SignContextAttrs<'input> for SignContext<'input>{}

pub type PlusSignContext<'input> = BaseParserRuleContext<'input,PlusSignContextExt<'input>>;

pub trait PlusSignContextAttrs<'input>: LibSLParserContext<'input>{
	/// Retrieves first TerminalNode corresponding to token PLUS
	/// Returns `None` if there is no child corresponding to token PLUS
	fn PLUS(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(PLUS, 0)
	}
}

impl<'input> PlusSignContextAttrs<'input> for PlusSignContext<'input>{}

pub struct PlusSignContextExt<'input>{
	__base:SignContextExt<'input>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{PlusSignContextExt<'a>}

impl<'input> LibSLParserContext<'input> for PlusSignContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for PlusSignContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_PlusSign(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_PlusSign(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for PlusSignContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_sign }
	//fn type_rule_index() -> usize where Self: Sized { RULE_sign }
}

impl<'input> Borrow<SignContextExt<'input>> for PlusSignContext<'input>{
	fn borrow(&self) -> &SignContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<SignContextExt<'input>> for PlusSignContext<'input>{
	fn borrow_mut(&mut self) -> &mut SignContextExt<'input> { &mut self.__base }
}

impl<'input> SignContextAttrs<'input> for PlusSignContext<'input> {}

impl<'input> PlusSignContextExt<'input>{
	fn new(ctx: &dyn SignContextAttrs<'input>) -> Rc<SignContextAll<'input>>  {
		Rc::new(
			SignContextAll::PlusSignContext(
				BaseParserRuleContext::copy_from(ctx,PlusSignContextExt{
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type MinusSignContext<'input> = BaseParserRuleContext<'input,MinusSignContextExt<'input>>;

pub trait MinusSignContextAttrs<'input>: LibSLParserContext<'input>{
	/// Retrieves first TerminalNode corresponding to token MINUS
	/// Returns `None` if there is no child corresponding to token MINUS
	fn MINUS(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(MINUS, 0)
	}
}

impl<'input> MinusSignContextAttrs<'input> for MinusSignContext<'input>{}

pub struct MinusSignContextExt<'input>{
	__base:SignContextExt<'input>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{MinusSignContextExt<'a>}

impl<'input> LibSLParserContext<'input> for MinusSignContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for MinusSignContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_MinusSign(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_MinusSign(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for MinusSignContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_sign }
	//fn type_rule_index() -> usize where Self: Sized { RULE_sign }
}

impl<'input> Borrow<SignContextExt<'input>> for MinusSignContext<'input>{
	fn borrow(&self) -> &SignContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<SignContextExt<'input>> for MinusSignContext<'input>{
	fn borrow_mut(&mut self) -> &mut SignContextExt<'input> { &mut self.__base }
}

impl<'input> SignContextAttrs<'input> for MinusSignContext<'input> {}

impl<'input> MinusSignContextExt<'input>{
	fn new(ctx: &dyn SignContextAttrs<'input>) -> Rc<SignContextAll<'input>>  {
		Rc::new(
			SignContextAll::MinusSignContext(
				BaseParserRuleContext::copy_from(ctx,MinusSignContextExt{
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

impl<'input, I, H> LibSLParser<'input, I, H>
where
    I: TokenStream<'input, TF = LocalTokenFactory<'input> > + TidAble<'input>,
    H: ErrorStrategy<'input,BaseParserType<'input,I>>
{
	pub fn sign(&mut self,)
	-> Result<Rc<SignContextAll<'input>>,ANTLRError> {
		let mut recog = self;
		let _parentctx = recog.ctx.take();
		let mut _localctx = SignContextExt::new(_parentctx.clone(), recog.base.get_state());
        recog.base.enter_rule(_localctx.clone(), 34, RULE_sign);
        let mut _localctx: Rc<SignContextAll> = _localctx;
		let result: Result<(), ANTLRError> = (|| {

			recog.base.set_state(381);
			recog.err_handler.sync(&mut recog.base)?;
			match recog.base.input.la(1) {
			 MINUS 
				=> {
					let tmp = MinusSignContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 1);
					_localctx = tmp;
					{
					recog.base.set_state(379);
					recog.base.match_token(MINUS,&mut recog.err_handler)?;

					}
				}

			 PLUS 
				=> {
					let tmp = PlusSignContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 2);
					_localctx = tmp;
					{
					recog.base.set_state(380);
					recog.base.match_token(PLUS,&mut recog.err_handler)?;

					}
				}

				_ => Err(ANTLRError::NoAltError(NoViableAltError::new(&mut recog.base)))?
			}
			Ok(())
		})();
		match result {
		Ok(_)=>{},
        Err(e @ ANTLRError::FallThrough(_)) => return Err(e),
		Err(ref re) => {
				//_localctx.exception = re;
				recog.err_handler.report_error(&mut recog.base, re);
				recog.err_handler.recover(&mut recog.base, re)?;
			}
		}
		recog.base.exit_rule();

		Ok(_localctx)
	}
}
//------------------- annotationDecl ----------------
pub type AnnotationDeclContextAll<'input> = AnnotationDeclContext<'input>;


pub type AnnotationDeclContext<'input> = BaseParserRuleContext<'input,AnnotationDeclContextExt<'input>>;

#[derive(Clone)]
pub struct AnnotationDeclContextExt<'input>{
	pub name: Option<Rc<IdentContextAll<'input>>>,
	pub params: Option<Rc<AnnotationParamListContextAll<'input>>>,
ph:PhantomData<&'input str>
}

impl<'input> LibSLParserContext<'input> for AnnotationDeclContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for AnnotationDeclContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_annotationDecl(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_annotationDecl(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for AnnotationDeclContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_annotationDecl }
	//fn type_rule_index() -> usize where Self: Sized { RULE_annotationDecl }
}
antlr_rust::tid!{AnnotationDeclContextExt<'a>}

impl<'input> AnnotationDeclContextExt<'input>{
	fn new(parent: Option<Rc<dyn LibSLParserContext<'input> + 'input > >, invoking_state: isize) -> Rc<AnnotationDeclContextAll<'input>> {
		Rc::new(
			BaseParserRuleContext::new_parser_ctx(parent, invoking_state,AnnotationDeclContextExt{
				name: None, params: None, 
				ph:PhantomData
			}),
		)
	}
}

pub trait AnnotationDeclContextAttrs<'input>: LibSLParserContext<'input> + BorrowMut<AnnotationDeclContextExt<'input>>{

/// Retrieves first TerminalNode corresponding to token ANNOTATION
/// Returns `None` if there is no child corresponding to token ANNOTATION
fn ANNOTATION(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(ANNOTATION, 0)
}
/// Retrieves first TerminalNode corresponding to token L_PAREN
/// Returns `None` if there is no child corresponding to token L_PAREN
fn L_PAREN(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(L_PAREN, 0)
}
/// Retrieves first TerminalNode corresponding to token R_PAREN
/// Returns `None` if there is no child corresponding to token R_PAREN
fn R_PAREN(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(R_PAREN, 0)
}
/// Retrieves first TerminalNode corresponding to token SEMICOLON
/// Returns `None` if there is no child corresponding to token SEMICOLON
fn SEMICOLON(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(SEMICOLON, 0)
}
fn ident(&self) -> Option<Rc<IdentContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}
fn annotationParamList(&self) -> Option<Rc<AnnotationParamListContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}
/// Retrieves first TerminalNode corresponding to token COMMA
/// Returns `None` if there is no child corresponding to token COMMA
fn COMMA(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(COMMA, 0)
}

}

impl<'input> AnnotationDeclContextAttrs<'input> for AnnotationDeclContext<'input>{}

impl<'input, I, H> LibSLParser<'input, I, H>
where
    I: TokenStream<'input, TF = LocalTokenFactory<'input> > + TidAble<'input>,
    H: ErrorStrategy<'input,BaseParserType<'input,I>>
{
	pub fn annotationDecl(&mut self,)
	-> Result<Rc<AnnotationDeclContextAll<'input>>,ANTLRError> {
		let mut recog = self;
		let _parentctx = recog.ctx.take();
		let mut _localctx = AnnotationDeclContextExt::new(_parentctx.clone(), recog.base.get_state());
        recog.base.enter_rule(_localctx.clone(), 36, RULE_annotationDecl);
        let mut _localctx: Rc<AnnotationDeclContextAll> = _localctx;
		let mut _la: isize = -1;
		let result: Result<(), ANTLRError> = (|| {

			//recog.base.enter_outer_alt(_localctx.clone(), 1);
			recog.base.enter_outer_alt(None, 1);
			{
			recog.base.set_state(383);
			recog.base.match_token(ANNOTATION,&mut recog.err_handler)?;

			/*InvokeRule ident*/
			recog.base.set_state(384);
			let tmp = recog.ident()?;
			 cast_mut::<_,AnnotationDeclContext >(&mut _localctx).name = Some(tmp.clone());
			  

			recog.base.set_state(385);
			recog.base.match_token(L_PAREN,&mut recog.err_handler)?;

			recog.base.set_state(390);
			recog.err_handler.sync(&mut recog.base)?;
			_la = recog.base.input.la(1);
			if ((((_la - 86)) & !0x3f) == 0 && ((1usize << (_la - 86)) & 519) != 0) {
				{
				/*InvokeRule annotationParamList*/
				recog.base.set_state(386);
				let tmp = recog.annotationParamList()?;
				 cast_mut::<_,AnnotationDeclContext >(&mut _localctx).params = Some(tmp.clone());
				  

				recog.base.set_state(388);
				recog.err_handler.sync(&mut recog.base)?;
				_la = recog.base.input.la(1);
				if _la==COMMA {
					{
					recog.base.set_state(387);
					recog.base.match_token(COMMA,&mut recog.err_handler)?;

					}
				}

				}
			}

			recog.base.set_state(392);
			recog.base.match_token(R_PAREN,&mut recog.err_handler)?;

			recog.base.set_state(393);
			recog.base.match_token(SEMICOLON,&mut recog.err_handler)?;

			}
			Ok(())
		})();
		match result {
		Ok(_)=>{},
        Err(e @ ANTLRError::FallThrough(_)) => return Err(e),
		Err(ref re) => {
				//_localctx.exception = re;
				recog.err_handler.report_error(&mut recog.base, re);
				recog.err_handler.recover(&mut recog.base, re)?;
			}
		}
		recog.base.exit_rule();

		Ok(_localctx)
	}
}
//------------------- annotationParamList ----------------
pub type AnnotationParamListContextAll<'input> = AnnotationParamListContext<'input>;


pub type AnnotationParamListContext<'input> = BaseParserRuleContext<'input,AnnotationParamListContextExt<'input>>;

#[derive(Clone)]
pub struct AnnotationParamListContextExt<'input>{
	pub annotationParam: Option<Rc<AnnotationParamContextAll<'input>>>,
	pub params:Vec<Rc<AnnotationParamContextAll<'input>>>,
ph:PhantomData<&'input str>
}

impl<'input> LibSLParserContext<'input> for AnnotationParamListContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for AnnotationParamListContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_annotationParamList(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_annotationParamList(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for AnnotationParamListContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_annotationParamList }
	//fn type_rule_index() -> usize where Self: Sized { RULE_annotationParamList }
}
antlr_rust::tid!{AnnotationParamListContextExt<'a>}

impl<'input> AnnotationParamListContextExt<'input>{
	fn new(parent: Option<Rc<dyn LibSLParserContext<'input> + 'input > >, invoking_state: isize) -> Rc<AnnotationParamListContextAll<'input>> {
		Rc::new(
			BaseParserRuleContext::new_parser_ctx(parent, invoking_state,AnnotationParamListContextExt{
				annotationParam: None, 
				params: Vec::new(), 
				ph:PhantomData
			}),
		)
	}
}

pub trait AnnotationParamListContextAttrs<'input>: LibSLParserContext<'input> + BorrowMut<AnnotationParamListContextExt<'input>>{

fn annotationParam_all(&self) ->  Vec<Rc<AnnotationParamContextAll<'input>>> where Self:Sized{
	self.children_of_type()
}
fn annotationParam(&self, i: usize) -> Option<Rc<AnnotationParamContextAll<'input>>> where Self:Sized{
	self.child_of_type(i)
}
/// Retrieves all `TerminalNode`s corresponding to token COMMA in current rule
fn COMMA_all(&self) -> Vec<Rc<TerminalNode<'input,LibSLParserContextType>>>  where Self:Sized{
	self.get_tokens(COMMA)
}
/// Retrieves 'i's TerminalNode corresponding to token COMMA, starting from 0.
/// Returns `None` if number of children corresponding to token COMMA is less or equal than `i`.
fn COMMA(&self, i: usize) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(COMMA, i)
}

}

impl<'input> AnnotationParamListContextAttrs<'input> for AnnotationParamListContext<'input>{}

impl<'input, I, H> LibSLParser<'input, I, H>
where
    I: TokenStream<'input, TF = LocalTokenFactory<'input> > + TidAble<'input>,
    H: ErrorStrategy<'input,BaseParserType<'input,I>>
{
	pub fn annotationParamList(&mut self,)
	-> Result<Rc<AnnotationParamListContextAll<'input>>,ANTLRError> {
		let mut recog = self;
		let _parentctx = recog.ctx.take();
		let mut _localctx = AnnotationParamListContextExt::new(_parentctx.clone(), recog.base.get_state());
        recog.base.enter_rule(_localctx.clone(), 38, RULE_annotationParamList);
        let mut _localctx: Rc<AnnotationParamListContextAll> = _localctx;
		let result: Result<(), ANTLRError> = (|| {

			let mut _alt: isize;
			//recog.base.enter_outer_alt(_localctx.clone(), 1);
			recog.base.enter_outer_alt(None, 1);
			{
			/*InvokeRule annotationParam*/
			recog.base.set_state(395);
			let tmp = recog.annotationParam()?;
			 cast_mut::<_,AnnotationParamListContext >(&mut _localctx).annotationParam = Some(tmp.clone());
			  

			let temp =  cast_mut::<_,AnnotationParamListContext >(&mut _localctx).annotationParam.clone().unwrap()
			 ;
			 cast_mut::<_,AnnotationParamListContext >(&mut _localctx).params.push(temp);
			  
			recog.base.set_state(400);
			recog.err_handler.sync(&mut recog.base)?;
			_alt = recog.interpreter.adaptive_predict(26,&mut recog.base)?;
			while { _alt!=2 && _alt!=INVALID_ALT } {
				if _alt==1 {
					{
					{
					recog.base.set_state(396);
					recog.base.match_token(COMMA,&mut recog.err_handler)?;

					/*InvokeRule annotationParam*/
					recog.base.set_state(397);
					let tmp = recog.annotationParam()?;
					 cast_mut::<_,AnnotationParamListContext >(&mut _localctx).annotationParam = Some(tmp.clone());
					  

					let temp =  cast_mut::<_,AnnotationParamListContext >(&mut _localctx).annotationParam.clone().unwrap()
					 ;
					 cast_mut::<_,AnnotationParamListContext >(&mut _localctx).params.push(temp);
					  
					}
					} 
				}
				recog.base.set_state(402);
				recog.err_handler.sync(&mut recog.base)?;
				_alt = recog.interpreter.adaptive_predict(26,&mut recog.base)?;
			}
			}
			Ok(())
		})();
		match result {
		Ok(_)=>{},
        Err(e @ ANTLRError::FallThrough(_)) => return Err(e),
		Err(ref re) => {
				//_localctx.exception = re;
				recog.err_handler.report_error(&mut recog.base, re);
				recog.err_handler.recover(&mut recog.base, re)?;
			}
		}
		recog.base.exit_rule();

		Ok(_localctx)
	}
}
//------------------- annotationParam ----------------
pub type AnnotationParamContextAll<'input> = AnnotationParamContext<'input>;


pub type AnnotationParamContext<'input> = BaseParserRuleContext<'input,AnnotationParamContextExt<'input>>;

#[derive(Clone)]
pub struct AnnotationParamContextExt<'input>{
	pub name: Option<Rc<IdentContextAll<'input>>>,
	pub r#type: Option<Rc<TypeExprContextAll<'input>>>,
	pub default: Option<Rc<ExprContextAll<'input>>>,
ph:PhantomData<&'input str>
}

impl<'input> LibSLParserContext<'input> for AnnotationParamContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for AnnotationParamContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_annotationParam(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_annotationParam(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for AnnotationParamContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_annotationParam }
	//fn type_rule_index() -> usize where Self: Sized { RULE_annotationParam }
}
antlr_rust::tid!{AnnotationParamContextExt<'a>}

impl<'input> AnnotationParamContextExt<'input>{
	fn new(parent: Option<Rc<dyn LibSLParserContext<'input> + 'input > >, invoking_state: isize) -> Rc<AnnotationParamContextAll<'input>> {
		Rc::new(
			BaseParserRuleContext::new_parser_ctx(parent, invoking_state,AnnotationParamContextExt{
				name: None, r#type: None, default: None, 
				ph:PhantomData
			}),
		)
	}
}

pub trait AnnotationParamContextAttrs<'input>: LibSLParserContext<'input> + BorrowMut<AnnotationParamContextExt<'input>>{

/// Retrieves first TerminalNode corresponding to token COLON
/// Returns `None` if there is no child corresponding to token COLON
fn COLON(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(COLON, 0)
}
fn ident(&self) -> Option<Rc<IdentContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}
fn typeExpr(&self) -> Option<Rc<TypeExprContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}
/// Retrieves first TerminalNode corresponding to token EQ
/// Returns `None` if there is no child corresponding to token EQ
fn EQ(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(EQ, 0)
}
fn expr(&self) -> Option<Rc<ExprContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}

}

impl<'input> AnnotationParamContextAttrs<'input> for AnnotationParamContext<'input>{}

impl<'input, I, H> LibSLParser<'input, I, H>
where
    I: TokenStream<'input, TF = LocalTokenFactory<'input> > + TidAble<'input>,
    H: ErrorStrategy<'input,BaseParserType<'input,I>>
{
	pub fn annotationParam(&mut self,)
	-> Result<Rc<AnnotationParamContextAll<'input>>,ANTLRError> {
		let mut recog = self;
		let _parentctx = recog.ctx.take();
		let mut _localctx = AnnotationParamContextExt::new(_parentctx.clone(), recog.base.get_state());
        recog.base.enter_rule(_localctx.clone(), 40, RULE_annotationParam);
        let mut _localctx: Rc<AnnotationParamContextAll> = _localctx;
		let mut _la: isize = -1;
		let result: Result<(), ANTLRError> = (|| {

			//recog.base.enter_outer_alt(_localctx.clone(), 1);
			recog.base.enter_outer_alt(None, 1);
			{
			/*InvokeRule ident*/
			recog.base.set_state(403);
			let tmp = recog.ident()?;
			 cast_mut::<_,AnnotationParamContext >(&mut _localctx).name = Some(tmp.clone());
			  

			recog.base.set_state(404);
			recog.base.match_token(COLON,&mut recog.err_handler)?;

			/*InvokeRule typeExpr*/
			recog.base.set_state(405);
			let tmp = recog.typeExpr_rec(0)?;
			 cast_mut::<_,AnnotationParamContext >(&mut _localctx).r#type = Some(tmp.clone());
			  

			recog.base.set_state(408);
			recog.err_handler.sync(&mut recog.base)?;
			_la = recog.base.input.la(1);
			if _la==EQ {
				{
				recog.base.set_state(406);
				recog.base.match_token(EQ,&mut recog.err_handler)?;

				/*InvokeRule expr*/
				recog.base.set_state(407);
				let tmp = recog.expr_rec(0)?;
				 cast_mut::<_,AnnotationParamContext >(&mut _localctx).default = Some(tmp.clone());
				  

				}
			}

			}
			Ok(())
		})();
		match result {
		Ok(_)=>{},
        Err(e @ ANTLRError::FallThrough(_)) => return Err(e),
		Err(ref re) => {
				//_localctx.exception = re;
				recog.err_handler.report_error(&mut recog.base, re);
				recog.err_handler.recover(&mut recog.base, re)?;
			}
		}
		recog.base.exit_rule();

		Ok(_localctx)
	}
}
//------------------- actionDecl ----------------
pub type ActionDeclContextAll<'input> = ActionDeclContext<'input>;


pub type ActionDeclContext<'input> = BaseParserRuleContext<'input,ActionDeclContextExt<'input>>;

#[derive(Clone)]
pub struct ActionDeclContextExt<'input>{
	pub annotation: Option<Rc<AnnotationContextAll<'input>>>,
	pub annotations:Vec<Rc<AnnotationContextAll<'input>>>,
	pub name: Option<Rc<IdentContextAll<'input>>>,
	pub typeParams: Option<Rc<GenericsContextAll<'input>>>,
	pub params: Option<Rc<ActionParamListContextAll<'input>>>,
	pub retType: Option<Rc<TypeExprContextAll<'input>>>,
	pub typeConstrants: Option<Rc<WhereClauseContextAll<'input>>>,
ph:PhantomData<&'input str>
}

impl<'input> LibSLParserContext<'input> for ActionDeclContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for ActionDeclContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_actionDecl(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_actionDecl(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for ActionDeclContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_actionDecl }
	//fn type_rule_index() -> usize where Self: Sized { RULE_actionDecl }
}
antlr_rust::tid!{ActionDeclContextExt<'a>}

impl<'input> ActionDeclContextExt<'input>{
	fn new(parent: Option<Rc<dyn LibSLParserContext<'input> + 'input > >, invoking_state: isize) -> Rc<ActionDeclContextAll<'input>> {
		Rc::new(
			BaseParserRuleContext::new_parser_ctx(parent, invoking_state,ActionDeclContextExt{
				annotation: None, name: None, typeParams: None, params: None, retType: None, typeConstrants: None, 
				annotations: Vec::new(), 
				ph:PhantomData
			}),
		)
	}
}

pub trait ActionDeclContextAttrs<'input>: LibSLParserContext<'input> + BorrowMut<ActionDeclContextExt<'input>>{

/// Retrieves first TerminalNode corresponding to token DEFINE
/// Returns `None` if there is no child corresponding to token DEFINE
fn DEFINE(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(DEFINE, 0)
}
/// Retrieves first TerminalNode corresponding to token ACTION
/// Returns `None` if there is no child corresponding to token ACTION
fn ACTION(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(ACTION, 0)
}
/// Retrieves first TerminalNode corresponding to token L_PAREN
/// Returns `None` if there is no child corresponding to token L_PAREN
fn L_PAREN(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(L_PAREN, 0)
}
/// Retrieves first TerminalNode corresponding to token R_PAREN
/// Returns `None` if there is no child corresponding to token R_PAREN
fn R_PAREN(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(R_PAREN, 0)
}
/// Retrieves first TerminalNode corresponding to token SEMICOLON
/// Returns `None` if there is no child corresponding to token SEMICOLON
fn SEMICOLON(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(SEMICOLON, 0)
}
fn ident(&self) -> Option<Rc<IdentContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}
/// Retrieves first TerminalNode corresponding to token COLON
/// Returns `None` if there is no child corresponding to token COLON
fn COLON(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(COLON, 0)
}
fn annotation_all(&self) ->  Vec<Rc<AnnotationContextAll<'input>>> where Self:Sized{
	self.children_of_type()
}
fn annotation(&self, i: usize) -> Option<Rc<AnnotationContextAll<'input>>> where Self:Sized{
	self.child_of_type(i)
}
fn generics(&self) -> Option<Rc<GenericsContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}
fn actionParamList(&self) -> Option<Rc<ActionParamListContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}
fn typeExpr(&self) -> Option<Rc<TypeExprContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}
fn whereClause(&self) -> Option<Rc<WhereClauseContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}
/// Retrieves first TerminalNode corresponding to token COMMA
/// Returns `None` if there is no child corresponding to token COMMA
fn COMMA(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(COMMA, 0)
}

}

impl<'input> ActionDeclContextAttrs<'input> for ActionDeclContext<'input>{}

impl<'input, I, H> LibSLParser<'input, I, H>
where
    I: TokenStream<'input, TF = LocalTokenFactory<'input> > + TidAble<'input>,
    H: ErrorStrategy<'input,BaseParserType<'input,I>>
{
	pub fn actionDecl(&mut self,)
	-> Result<Rc<ActionDeclContextAll<'input>>,ANTLRError> {
		let mut recog = self;
		let _parentctx = recog.ctx.take();
		let mut _localctx = ActionDeclContextExt::new(_parentctx.clone(), recog.base.get_state());
        recog.base.enter_rule(_localctx.clone(), 42, RULE_actionDecl);
        let mut _localctx: Rc<ActionDeclContextAll> = _localctx;
		let mut _la: isize = -1;
		let result: Result<(), ANTLRError> = (|| {

			//recog.base.enter_outer_alt(_localctx.clone(), 1);
			recog.base.enter_outer_alt(None, 1);
			{
			recog.base.set_state(413);
			recog.err_handler.sync(&mut recog.base)?;
			_la = recog.base.input.la(1);
			while _la==AT {
				{
				{
				/*InvokeRule annotation*/
				recog.base.set_state(410);
				let tmp = recog.annotation()?;
				 cast_mut::<_,ActionDeclContext >(&mut _localctx).annotation = Some(tmp.clone());
				  

				let temp =  cast_mut::<_,ActionDeclContext >(&mut _localctx).annotation.clone().unwrap()
				 ;
				 cast_mut::<_,ActionDeclContext >(&mut _localctx).annotations.push(temp);
				  
				}
				}
				recog.base.set_state(415);
				recog.err_handler.sync(&mut recog.base)?;
				_la = recog.base.input.la(1);
			}
			recog.base.set_state(416);
			recog.base.match_token(DEFINE,&mut recog.err_handler)?;

			recog.base.set_state(417);
			recog.base.match_token(ACTION,&mut recog.err_handler)?;

			/*InvokeRule ident*/
			recog.base.set_state(418);
			let tmp = recog.ident()?;
			 cast_mut::<_,ActionDeclContext >(&mut _localctx).name = Some(tmp.clone());
			  

			recog.base.set_state(420);
			recog.err_handler.sync(&mut recog.base)?;
			_la = recog.base.input.la(1);
			if _la==L_ANGLE {
				{
				/*InvokeRule generics*/
				recog.base.set_state(419);
				let tmp = recog.generics()?;
				 cast_mut::<_,ActionDeclContext >(&mut _localctx).typeParams = Some(tmp.clone());
				  

				}
			}

			recog.base.set_state(422);
			recog.base.match_token(L_PAREN,&mut recog.err_handler)?;

			recog.base.set_state(427);
			recog.err_handler.sync(&mut recog.base)?;
			_la = recog.base.input.la(1);
			if ((((_la - 86)) & !0x3f) == 0 && ((1usize << (_la - 86)) & 647) != 0) {
				{
				/*InvokeRule actionParamList*/
				recog.base.set_state(423);
				let tmp = recog.actionParamList()?;
				 cast_mut::<_,ActionDeclContext >(&mut _localctx).params = Some(tmp.clone());
				  

				recog.base.set_state(425);
				recog.err_handler.sync(&mut recog.base)?;
				_la = recog.base.input.la(1);
				if _la==COMMA {
					{
					recog.base.set_state(424);
					recog.base.match_token(COMMA,&mut recog.err_handler)?;

					}
				}

				}
			}

			recog.base.set_state(429);
			recog.base.match_token(R_PAREN,&mut recog.err_handler)?;

			recog.base.set_state(432);
			recog.err_handler.sync(&mut recog.base)?;
			_la = recog.base.input.la(1);
			if _la==COLON {
				{
				recog.base.set_state(430);
				recog.base.match_token(COLON,&mut recog.err_handler)?;

				/*InvokeRule typeExpr*/
				recog.base.set_state(431);
				let tmp = recog.typeExpr_rec(0)?;
				 cast_mut::<_,ActionDeclContext >(&mut _localctx).retType = Some(tmp.clone());
				  

				}
			}

			recog.base.set_state(435);
			recog.err_handler.sync(&mut recog.base)?;
			_la = recog.base.input.la(1);
			if _la==WHERE {
				{
				/*InvokeRule whereClause*/
				recog.base.set_state(434);
				let tmp = recog.whereClause()?;
				 cast_mut::<_,ActionDeclContext >(&mut _localctx).typeConstrants = Some(tmp.clone());
				  

				}
			}

			recog.base.set_state(437);
			recog.base.match_token(SEMICOLON,&mut recog.err_handler)?;

			}
			Ok(())
		})();
		match result {
		Ok(_)=>{},
        Err(e @ ANTLRError::FallThrough(_)) => return Err(e),
		Err(ref re) => {
				//_localctx.exception = re;
				recog.err_handler.report_error(&mut recog.base, re);
				recog.err_handler.recover(&mut recog.base, re)?;
			}
		}
		recog.base.exit_rule();

		Ok(_localctx)
	}
}
//------------------- actionParamList ----------------
pub type ActionParamListContextAll<'input> = ActionParamListContext<'input>;


pub type ActionParamListContext<'input> = BaseParserRuleContext<'input,ActionParamListContextExt<'input>>;

#[derive(Clone)]
pub struct ActionParamListContextExt<'input>{
	pub actionParam: Option<Rc<ActionParamContextAll<'input>>>,
	pub params:Vec<Rc<ActionParamContextAll<'input>>>,
ph:PhantomData<&'input str>
}

impl<'input> LibSLParserContext<'input> for ActionParamListContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for ActionParamListContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_actionParamList(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_actionParamList(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for ActionParamListContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_actionParamList }
	//fn type_rule_index() -> usize where Self: Sized { RULE_actionParamList }
}
antlr_rust::tid!{ActionParamListContextExt<'a>}

impl<'input> ActionParamListContextExt<'input>{
	fn new(parent: Option<Rc<dyn LibSLParserContext<'input> + 'input > >, invoking_state: isize) -> Rc<ActionParamListContextAll<'input>> {
		Rc::new(
			BaseParserRuleContext::new_parser_ctx(parent, invoking_state,ActionParamListContextExt{
				actionParam: None, 
				params: Vec::new(), 
				ph:PhantomData
			}),
		)
	}
}

pub trait ActionParamListContextAttrs<'input>: LibSLParserContext<'input> + BorrowMut<ActionParamListContextExt<'input>>{

fn actionParam_all(&self) ->  Vec<Rc<ActionParamContextAll<'input>>> where Self:Sized{
	self.children_of_type()
}
fn actionParam(&self, i: usize) -> Option<Rc<ActionParamContextAll<'input>>> where Self:Sized{
	self.child_of_type(i)
}
/// Retrieves all `TerminalNode`s corresponding to token COMMA in current rule
fn COMMA_all(&self) -> Vec<Rc<TerminalNode<'input,LibSLParserContextType>>>  where Self:Sized{
	self.get_tokens(COMMA)
}
/// Retrieves 'i's TerminalNode corresponding to token COMMA, starting from 0.
/// Returns `None` if number of children corresponding to token COMMA is less or equal than `i`.
fn COMMA(&self, i: usize) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(COMMA, i)
}

}

impl<'input> ActionParamListContextAttrs<'input> for ActionParamListContext<'input>{}

impl<'input, I, H> LibSLParser<'input, I, H>
where
    I: TokenStream<'input, TF = LocalTokenFactory<'input> > + TidAble<'input>,
    H: ErrorStrategy<'input,BaseParserType<'input,I>>
{
	pub fn actionParamList(&mut self,)
	-> Result<Rc<ActionParamListContextAll<'input>>,ANTLRError> {
		let mut recog = self;
		let _parentctx = recog.ctx.take();
		let mut _localctx = ActionParamListContextExt::new(_parentctx.clone(), recog.base.get_state());
        recog.base.enter_rule(_localctx.clone(), 44, RULE_actionParamList);
        let mut _localctx: Rc<ActionParamListContextAll> = _localctx;
		let result: Result<(), ANTLRError> = (|| {

			let mut _alt: isize;
			//recog.base.enter_outer_alt(_localctx.clone(), 1);
			recog.base.enter_outer_alt(None, 1);
			{
			/*InvokeRule actionParam*/
			recog.base.set_state(439);
			let tmp = recog.actionParam()?;
			 cast_mut::<_,ActionParamListContext >(&mut _localctx).actionParam = Some(tmp.clone());
			  

			let temp =  cast_mut::<_,ActionParamListContext >(&mut _localctx).actionParam.clone().unwrap()
			 ;
			 cast_mut::<_,ActionParamListContext >(&mut _localctx).params.push(temp);
			  
			recog.base.set_state(444);
			recog.err_handler.sync(&mut recog.base)?;
			_alt = recog.interpreter.adaptive_predict(34,&mut recog.base)?;
			while { _alt!=2 && _alt!=INVALID_ALT } {
				if _alt==1 {
					{
					{
					recog.base.set_state(440);
					recog.base.match_token(COMMA,&mut recog.err_handler)?;

					/*InvokeRule actionParam*/
					recog.base.set_state(441);
					let tmp = recog.actionParam()?;
					 cast_mut::<_,ActionParamListContext >(&mut _localctx).actionParam = Some(tmp.clone());
					  

					let temp =  cast_mut::<_,ActionParamListContext >(&mut _localctx).actionParam.clone().unwrap()
					 ;
					 cast_mut::<_,ActionParamListContext >(&mut _localctx).params.push(temp);
					  
					}
					} 
				}
				recog.base.set_state(446);
				recog.err_handler.sync(&mut recog.base)?;
				_alt = recog.interpreter.adaptive_predict(34,&mut recog.base)?;
			}
			}
			Ok(())
		})();
		match result {
		Ok(_)=>{},
        Err(e @ ANTLRError::FallThrough(_)) => return Err(e),
		Err(ref re) => {
				//_localctx.exception = re;
				recog.err_handler.report_error(&mut recog.base, re);
				recog.err_handler.recover(&mut recog.base, re)?;
			}
		}
		recog.base.exit_rule();

		Ok(_localctx)
	}
}
//------------------- actionParam ----------------
pub type ActionParamContextAll<'input> = ActionParamContext<'input>;


pub type ActionParamContext<'input> = BaseParserRuleContext<'input,ActionParamContextExt<'input>>;

#[derive(Clone)]
pub struct ActionParamContextExt<'input>{
	pub annotation: Option<Rc<AnnotationContextAll<'input>>>,
	pub annotations:Vec<Rc<AnnotationContextAll<'input>>>,
	pub name: Option<Rc<IdentContextAll<'input>>>,
	pub r#type: Option<Rc<TypeExprContextAll<'input>>>,
ph:PhantomData<&'input str>
}

impl<'input> LibSLParserContext<'input> for ActionParamContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for ActionParamContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_actionParam(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_actionParam(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for ActionParamContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_actionParam }
	//fn type_rule_index() -> usize where Self: Sized { RULE_actionParam }
}
antlr_rust::tid!{ActionParamContextExt<'a>}

impl<'input> ActionParamContextExt<'input>{
	fn new(parent: Option<Rc<dyn LibSLParserContext<'input> + 'input > >, invoking_state: isize) -> Rc<ActionParamContextAll<'input>> {
		Rc::new(
			BaseParserRuleContext::new_parser_ctx(parent, invoking_state,ActionParamContextExt{
				annotation: None, name: None, r#type: None, 
				annotations: Vec::new(), 
				ph:PhantomData
			}),
		)
	}
}

pub trait ActionParamContextAttrs<'input>: LibSLParserContext<'input> + BorrowMut<ActionParamContextExt<'input>>{

/// Retrieves first TerminalNode corresponding to token COLON
/// Returns `None` if there is no child corresponding to token COLON
fn COLON(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(COLON, 0)
}
fn ident(&self) -> Option<Rc<IdentContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}
fn typeExpr(&self) -> Option<Rc<TypeExprContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}
fn annotation_all(&self) ->  Vec<Rc<AnnotationContextAll<'input>>> where Self:Sized{
	self.children_of_type()
}
fn annotation(&self, i: usize) -> Option<Rc<AnnotationContextAll<'input>>> where Self:Sized{
	self.child_of_type(i)
}

}

impl<'input> ActionParamContextAttrs<'input> for ActionParamContext<'input>{}

impl<'input, I, H> LibSLParser<'input, I, H>
where
    I: TokenStream<'input, TF = LocalTokenFactory<'input> > + TidAble<'input>,
    H: ErrorStrategy<'input,BaseParserType<'input,I>>
{
	pub fn actionParam(&mut self,)
	-> Result<Rc<ActionParamContextAll<'input>>,ANTLRError> {
		let mut recog = self;
		let _parentctx = recog.ctx.take();
		let mut _localctx = ActionParamContextExt::new(_parentctx.clone(), recog.base.get_state());
        recog.base.enter_rule(_localctx.clone(), 46, RULE_actionParam);
        let mut _localctx: Rc<ActionParamContextAll> = _localctx;
		let mut _la: isize = -1;
		let result: Result<(), ANTLRError> = (|| {

			//recog.base.enter_outer_alt(_localctx.clone(), 1);
			recog.base.enter_outer_alt(None, 1);
			{
			recog.base.set_state(450);
			recog.err_handler.sync(&mut recog.base)?;
			_la = recog.base.input.la(1);
			while _la==AT {
				{
				{
				/*InvokeRule annotation*/
				recog.base.set_state(447);
				let tmp = recog.annotation()?;
				 cast_mut::<_,ActionParamContext >(&mut _localctx).annotation = Some(tmp.clone());
				  

				let temp =  cast_mut::<_,ActionParamContext >(&mut _localctx).annotation.clone().unwrap()
				 ;
				 cast_mut::<_,ActionParamContext >(&mut _localctx).annotations.push(temp);
				  
				}
				}
				recog.base.set_state(452);
				recog.err_handler.sync(&mut recog.base)?;
				_la = recog.base.input.la(1);
			}
			/*InvokeRule ident*/
			recog.base.set_state(453);
			let tmp = recog.ident()?;
			 cast_mut::<_,ActionParamContext >(&mut _localctx).name = Some(tmp.clone());
			  

			recog.base.set_state(454);
			recog.base.match_token(COLON,&mut recog.err_handler)?;

			/*InvokeRule typeExpr*/
			recog.base.set_state(455);
			let tmp = recog.typeExpr_rec(0)?;
			 cast_mut::<_,ActionParamContext >(&mut _localctx).r#type = Some(tmp.clone());
			  

			}
			Ok(())
		})();
		match result {
		Ok(_)=>{},
        Err(e @ ANTLRError::FallThrough(_)) => return Err(e),
		Err(ref re) => {
				//_localctx.exception = re;
				recog.err_handler.report_error(&mut recog.base, re);
				recog.err_handler.recover(&mut recog.base, re)?;
			}
		}
		recog.base.exit_rule();

		Ok(_localctx)
	}
}
//------------------- automatonDecl ----------------
pub type AutomatonDeclContextAll<'input> = AutomatonDeclContext<'input>;


pub type AutomatonDeclContext<'input> = BaseParserRuleContext<'input,AutomatonDeclContextExt<'input>>;

#[derive(Clone)]
pub struct AutomatonDeclContextExt<'input>{
	pub annotation: Option<Rc<AnnotationContextAll<'input>>>,
	pub annotations:Vec<Rc<AnnotationContextAll<'input>>>,
	pub concept: Option<TokenType<'input>>,
	pub name: Option<Rc<QualifiedTypeNameContextAll<'input>>>,
	pub constructorVariables: Option<Rc<ConstructorVariableListContextAll<'input>>>,
	pub r#type: Option<Rc<TypeExprContextAll<'input>>>,
	pub implements: Option<Rc<ImplementedConceptsContextAll<'input>>>,
	pub typeConstraints: Option<Rc<WhereClauseContextAll<'input>>>,
	pub automatonDefDecl: Option<Rc<AutomatonDefDeclContextAll<'input>>>,
	pub decls:Vec<Rc<AutomatonDefDeclContextAll<'input>>>,
ph:PhantomData<&'input str>
}

impl<'input> LibSLParserContext<'input> for AutomatonDeclContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for AutomatonDeclContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_automatonDecl(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_automatonDecl(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for AutomatonDeclContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_automatonDecl }
	//fn type_rule_index() -> usize where Self: Sized { RULE_automatonDecl }
}
antlr_rust::tid!{AutomatonDeclContextExt<'a>}

impl<'input> AutomatonDeclContextExt<'input>{
	fn new(parent: Option<Rc<dyn LibSLParserContext<'input> + 'input > >, invoking_state: isize) -> Rc<AutomatonDeclContextAll<'input>> {
		Rc::new(
			BaseParserRuleContext::new_parser_ctx(parent, invoking_state,AutomatonDeclContextExt{
				concept: None, 
				annotation: None, name: None, constructorVariables: None, r#type: None, implements: None, typeConstraints: None, automatonDefDecl: None, 
				annotations: Vec::new(), decls: Vec::new(), 
				ph:PhantomData
			}),
		)
	}
}

pub trait AutomatonDeclContextAttrs<'input>: LibSLParserContext<'input> + BorrowMut<AutomatonDeclContextExt<'input>>{

/// Retrieves first TerminalNode corresponding to token AUTOMATON
/// Returns `None` if there is no child corresponding to token AUTOMATON
fn AUTOMATON(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(AUTOMATON, 0)
}
/// Retrieves first TerminalNode corresponding to token COLON
/// Returns `None` if there is no child corresponding to token COLON
fn COLON(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(COLON, 0)
}
/// Retrieves first TerminalNode corresponding to token L_BRACE
/// Returns `None` if there is no child corresponding to token L_BRACE
fn L_BRACE(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(L_BRACE, 0)
}
/// Retrieves first TerminalNode corresponding to token R_BRACE
/// Returns `None` if there is no child corresponding to token R_BRACE
fn R_BRACE(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(R_BRACE, 0)
}
fn qualifiedTypeName(&self) -> Option<Rc<QualifiedTypeNameContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}
fn typeExpr(&self) -> Option<Rc<TypeExprContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}
/// Retrieves first TerminalNode corresponding to token L_PAREN
/// Returns `None` if there is no child corresponding to token L_PAREN
fn L_PAREN(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(L_PAREN, 0)
}
/// Retrieves first TerminalNode corresponding to token R_PAREN
/// Returns `None` if there is no child corresponding to token R_PAREN
fn R_PAREN(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(R_PAREN, 0)
}
fn annotation_all(&self) ->  Vec<Rc<AnnotationContextAll<'input>>> where Self:Sized{
	self.children_of_type()
}
fn annotation(&self, i: usize) -> Option<Rc<AnnotationContextAll<'input>>> where Self:Sized{
	self.child_of_type(i)
}
/// Retrieves first TerminalNode corresponding to token CONCEPT
/// Returns `None` if there is no child corresponding to token CONCEPT
fn CONCEPT(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(CONCEPT, 0)
}
fn implementedConcepts_all(&self) ->  Vec<Rc<ImplementedConceptsContextAll<'input>>> where Self:Sized{
	self.children_of_type()
}
fn implementedConcepts(&self, i: usize) -> Option<Rc<ImplementedConceptsContextAll<'input>>> where Self:Sized{
	self.child_of_type(i)
}
fn whereClause(&self) -> Option<Rc<WhereClauseContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}
fn automatonDefDecl_all(&self) ->  Vec<Rc<AutomatonDefDeclContextAll<'input>>> where Self:Sized{
	self.children_of_type()
}
fn automatonDefDecl(&self, i: usize) -> Option<Rc<AutomatonDefDeclContextAll<'input>>> where Self:Sized{
	self.child_of_type(i)
}
/// Retrieves all `TerminalNode`s corresponding to token COMMA in current rule
fn COMMA_all(&self) -> Vec<Rc<TerminalNode<'input,LibSLParserContextType>>>  where Self:Sized{
	self.get_tokens(COMMA)
}
/// Retrieves 'i's TerminalNode corresponding to token COMMA, starting from 0.
/// Returns `None` if number of children corresponding to token COMMA is less or equal than `i`.
fn COMMA(&self, i: usize) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(COMMA, i)
}
fn constructorVariableList(&self) -> Option<Rc<ConstructorVariableListContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}

}

impl<'input> AutomatonDeclContextAttrs<'input> for AutomatonDeclContext<'input>{}

impl<'input, I, H> LibSLParser<'input, I, H>
where
    I: TokenStream<'input, TF = LocalTokenFactory<'input> > + TidAble<'input>,
    H: ErrorStrategy<'input,BaseParserType<'input,I>>
{
	pub fn automatonDecl(&mut self,)
	-> Result<Rc<AutomatonDeclContextAll<'input>>,ANTLRError> {
		let mut recog = self;
		let _parentctx = recog.ctx.take();
		let mut _localctx = AutomatonDeclContextExt::new(_parentctx.clone(), recog.base.get_state());
        recog.base.enter_rule(_localctx.clone(), 48, RULE_automatonDecl);
        let mut _localctx: Rc<AutomatonDeclContextAll> = _localctx;
		let mut _la: isize = -1;
		let result: Result<(), ANTLRError> = (|| {

			//recog.base.enter_outer_alt(_localctx.clone(), 1);
			recog.base.enter_outer_alt(None, 1);
			{
			recog.base.set_state(460);
			recog.err_handler.sync(&mut recog.base)?;
			_la = recog.base.input.la(1);
			while _la==AT {
				{
				{
				/*InvokeRule annotation*/
				recog.base.set_state(457);
				let tmp = recog.annotation()?;
				 cast_mut::<_,AutomatonDeclContext >(&mut _localctx).annotation = Some(tmp.clone());
				  

				let temp =  cast_mut::<_,AutomatonDeclContext >(&mut _localctx).annotation.clone().unwrap()
				 ;
				 cast_mut::<_,AutomatonDeclContext >(&mut _localctx).annotations.push(temp);
				  
				}
				}
				recog.base.set_state(462);
				recog.err_handler.sync(&mut recog.base)?;
				_la = recog.base.input.la(1);
			}
			recog.base.set_state(463);
			recog.base.match_token(AUTOMATON,&mut recog.err_handler)?;

			recog.base.set_state(465);
			recog.err_handler.sync(&mut recog.base)?;
			_la = recog.base.input.la(1);
			if _la==CONCEPT {
				{
				recog.base.set_state(464);
				let tmp = recog.base.match_token(CONCEPT,&mut recog.err_handler)?;
				 cast_mut::<_,AutomatonDeclContext >(&mut _localctx).concept = Some(tmp.clone());
				  

				}
			}

			/*InvokeRule qualifiedTypeName*/
			recog.base.set_state(467);
			let tmp = recog.qualifiedTypeName()?;
			 cast_mut::<_,AutomatonDeclContext >(&mut _localctx).name = Some(tmp.clone());
			  

			recog.base.set_state(476);
			recog.err_handler.sync(&mut recog.base)?;
			_la = recog.base.input.la(1);
			if _la==L_PAREN {
				{
				recog.base.set_state(468);
				recog.base.match_token(L_PAREN,&mut recog.err_handler)?;

				recog.base.set_state(473);
				recog.err_handler.sync(&mut recog.base)?;
				_la = recog.base.input.la(1);
				if _la==VAR || _la==VAL || _la==AT {
					{
					/*InvokeRule constructorVariableList*/
					recog.base.set_state(469);
					let tmp = recog.constructorVariableList()?;
					 cast_mut::<_,AutomatonDeclContext >(&mut _localctx).constructorVariables = Some(tmp.clone());
					  

					recog.base.set_state(471);
					recog.err_handler.sync(&mut recog.base)?;
					_la = recog.base.input.la(1);
					if _la==COMMA {
						{
						recog.base.set_state(470);
						recog.base.match_token(COMMA,&mut recog.err_handler)?;

						}
					}

					}
				}

				recog.base.set_state(475);
				recog.base.match_token(R_PAREN,&mut recog.err_handler)?;

				}
			}

			recog.base.set_state(478);
			recog.base.match_token(COLON,&mut recog.err_handler)?;

			/*InvokeRule typeExpr*/
			recog.base.set_state(479);
			let tmp = recog.typeExpr_rec(0)?;
			 cast_mut::<_,AutomatonDeclContext >(&mut _localctx).r#type = Some(tmp.clone());
			  

			recog.base.set_state(486);
			recog.err_handler.sync(&mut recog.base)?;
			_la = recog.base.input.la(1);
			while _la==IMPLEMENTS {
				{
				{
				/*InvokeRule implementedConcepts*/
				recog.base.set_state(480);
				let tmp = recog.implementedConcepts()?;
				 cast_mut::<_,AutomatonDeclContext >(&mut _localctx).implements = Some(tmp.clone());
				  

				recog.base.set_state(482);
				recog.err_handler.sync(&mut recog.base)?;
				_la = recog.base.input.la(1);
				if _la==COMMA {
					{
					recog.base.set_state(481);
					recog.base.match_token(COMMA,&mut recog.err_handler)?;

					}
				}

				}
				}
				recog.base.set_state(488);
				recog.err_handler.sync(&mut recog.base)?;
				_la = recog.base.input.la(1);
			}
			recog.base.set_state(490);
			recog.err_handler.sync(&mut recog.base)?;
			_la = recog.base.input.la(1);
			if _la==WHERE {
				{
				/*InvokeRule whereClause*/
				recog.base.set_state(489);
				let tmp = recog.whereClause()?;
				 cast_mut::<_,AutomatonDeclContext >(&mut _localctx).typeConstraints = Some(tmp.clone());
				  

				}
			}

			recog.base.set_state(492);
			recog.base.match_token(L_BRACE,&mut recog.err_handler)?;

			recog.base.set_state(496);
			recog.err_handler.sync(&mut recog.base)?;
			_la = recog.base.input.la(1);
			while ((((_la - 57)) & !0x3f) == 0 && ((1usize << (_la - 57)) & 3221229503) != 0) || _la==AT {
				{
				{
				/*InvokeRule automatonDefDecl*/
				recog.base.set_state(493);
				let tmp = recog.automatonDefDecl()?;
				 cast_mut::<_,AutomatonDeclContext >(&mut _localctx).automatonDefDecl = Some(tmp.clone());
				  

				let temp =  cast_mut::<_,AutomatonDeclContext >(&mut _localctx).automatonDefDecl.clone().unwrap()
				 ;
				 cast_mut::<_,AutomatonDeclContext >(&mut _localctx).decls.push(temp);
				  
				}
				}
				recog.base.set_state(498);
				recog.err_handler.sync(&mut recog.base)?;
				_la = recog.base.input.la(1);
			}
			recog.base.set_state(499);
			recog.base.match_token(R_BRACE,&mut recog.err_handler)?;

			}
			Ok(())
		})();
		match result {
		Ok(_)=>{},
        Err(e @ ANTLRError::FallThrough(_)) => return Err(e),
		Err(ref re) => {
				//_localctx.exception = re;
				recog.err_handler.report_error(&mut recog.base, re);
				recog.err_handler.recover(&mut recog.base, re)?;
			}
		}
		recog.base.exit_rule();

		Ok(_localctx)
	}
}
//------------------- constructorVariableList ----------------
pub type ConstructorVariableListContextAll<'input> = ConstructorVariableListContext<'input>;


pub type ConstructorVariableListContext<'input> = BaseParserRuleContext<'input,ConstructorVariableListContextExt<'input>>;

#[derive(Clone)]
pub struct ConstructorVariableListContextExt<'input>{
	pub constructorVariable: Option<Rc<ConstructorVariableContextAll<'input>>>,
	pub variables:Vec<Rc<ConstructorVariableContextAll<'input>>>,
ph:PhantomData<&'input str>
}

impl<'input> LibSLParserContext<'input> for ConstructorVariableListContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for ConstructorVariableListContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_constructorVariableList(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_constructorVariableList(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for ConstructorVariableListContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_constructorVariableList }
	//fn type_rule_index() -> usize where Self: Sized { RULE_constructorVariableList }
}
antlr_rust::tid!{ConstructorVariableListContextExt<'a>}

impl<'input> ConstructorVariableListContextExt<'input>{
	fn new(parent: Option<Rc<dyn LibSLParserContext<'input> + 'input > >, invoking_state: isize) -> Rc<ConstructorVariableListContextAll<'input>> {
		Rc::new(
			BaseParserRuleContext::new_parser_ctx(parent, invoking_state,ConstructorVariableListContextExt{
				constructorVariable: None, 
				variables: Vec::new(), 
				ph:PhantomData
			}),
		)
	}
}

pub trait ConstructorVariableListContextAttrs<'input>: LibSLParserContext<'input> + BorrowMut<ConstructorVariableListContextExt<'input>>{

fn constructorVariable_all(&self) ->  Vec<Rc<ConstructorVariableContextAll<'input>>> where Self:Sized{
	self.children_of_type()
}
fn constructorVariable(&self, i: usize) -> Option<Rc<ConstructorVariableContextAll<'input>>> where Self:Sized{
	self.child_of_type(i)
}
/// Retrieves all `TerminalNode`s corresponding to token COMMA in current rule
fn COMMA_all(&self) -> Vec<Rc<TerminalNode<'input,LibSLParserContextType>>>  where Self:Sized{
	self.get_tokens(COMMA)
}
/// Retrieves 'i's TerminalNode corresponding to token COMMA, starting from 0.
/// Returns `None` if number of children corresponding to token COMMA is less or equal than `i`.
fn COMMA(&self, i: usize) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(COMMA, i)
}

}

impl<'input> ConstructorVariableListContextAttrs<'input> for ConstructorVariableListContext<'input>{}

impl<'input, I, H> LibSLParser<'input, I, H>
where
    I: TokenStream<'input, TF = LocalTokenFactory<'input> > + TidAble<'input>,
    H: ErrorStrategy<'input,BaseParserType<'input,I>>
{
	pub fn constructorVariableList(&mut self,)
	-> Result<Rc<ConstructorVariableListContextAll<'input>>,ANTLRError> {
		let mut recog = self;
		let _parentctx = recog.ctx.take();
		let mut _localctx = ConstructorVariableListContextExt::new(_parentctx.clone(), recog.base.get_state());
        recog.base.enter_rule(_localctx.clone(), 50, RULE_constructorVariableList);
        let mut _localctx: Rc<ConstructorVariableListContextAll> = _localctx;
		let result: Result<(), ANTLRError> = (|| {

			let mut _alt: isize;
			//recog.base.enter_outer_alt(_localctx.clone(), 1);
			recog.base.enter_outer_alt(None, 1);
			{
			/*InvokeRule constructorVariable*/
			recog.base.set_state(501);
			let tmp = recog.constructorVariable()?;
			 cast_mut::<_,ConstructorVariableListContext >(&mut _localctx).constructorVariable = Some(tmp.clone());
			  

			let temp =  cast_mut::<_,ConstructorVariableListContext >(&mut _localctx).constructorVariable.clone().unwrap()
			 ;
			 cast_mut::<_,ConstructorVariableListContext >(&mut _localctx).variables.push(temp);
			  
			recog.base.set_state(506);
			recog.err_handler.sync(&mut recog.base)?;
			_alt = recog.interpreter.adaptive_predict(45,&mut recog.base)?;
			while { _alt!=2 && _alt!=INVALID_ALT } {
				if _alt==1 {
					{
					{
					recog.base.set_state(502);
					recog.base.match_token(COMMA,&mut recog.err_handler)?;

					/*InvokeRule constructorVariable*/
					recog.base.set_state(503);
					let tmp = recog.constructorVariable()?;
					 cast_mut::<_,ConstructorVariableListContext >(&mut _localctx).constructorVariable = Some(tmp.clone());
					  

					let temp =  cast_mut::<_,ConstructorVariableListContext >(&mut _localctx).constructorVariable.clone().unwrap()
					 ;
					 cast_mut::<_,ConstructorVariableListContext >(&mut _localctx).variables.push(temp);
					  
					}
					} 
				}
				recog.base.set_state(508);
				recog.err_handler.sync(&mut recog.base)?;
				_alt = recog.interpreter.adaptive_predict(45,&mut recog.base)?;
			}
			}
			Ok(())
		})();
		match result {
		Ok(_)=>{},
        Err(e @ ANTLRError::FallThrough(_)) => return Err(e),
		Err(ref re) => {
				//_localctx.exception = re;
				recog.err_handler.report_error(&mut recog.base, re);
				recog.err_handler.recover(&mut recog.base, re)?;
			}
		}
		recog.base.exit_rule();

		Ok(_localctx)
	}
}
//------------------- constructorVariable ----------------
pub type ConstructorVariableContextAll<'input> = ConstructorVariableContext<'input>;


pub type ConstructorVariableContext<'input> = BaseParserRuleContext<'input,ConstructorVariableContextExt<'input>>;

#[derive(Clone)]
pub struct ConstructorVariableContextExt<'input>{
	pub annotation: Option<Rc<AnnotationContextAll<'input>>>,
	pub annotations:Vec<Rc<AnnotationContextAll<'input>>>,
	pub kind: Option<Rc<VariableKindContextAll<'input>>>,
	pub name: Option<Rc<IdentContextAll<'input>>>,
	pub r#type: Option<Rc<TypeExprContextAll<'input>>>,
	pub init: Option<Rc<ExprContextAll<'input>>>,
ph:PhantomData<&'input str>
}

impl<'input> LibSLParserContext<'input> for ConstructorVariableContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for ConstructorVariableContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_constructorVariable(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_constructorVariable(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for ConstructorVariableContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_constructorVariable }
	//fn type_rule_index() -> usize where Self: Sized { RULE_constructorVariable }
}
antlr_rust::tid!{ConstructorVariableContextExt<'a>}

impl<'input> ConstructorVariableContextExt<'input>{
	fn new(parent: Option<Rc<dyn LibSLParserContext<'input> + 'input > >, invoking_state: isize) -> Rc<ConstructorVariableContextAll<'input>> {
		Rc::new(
			BaseParserRuleContext::new_parser_ctx(parent, invoking_state,ConstructorVariableContextExt{
				annotation: None, kind: None, name: None, r#type: None, init: None, 
				annotations: Vec::new(), 
				ph:PhantomData
			}),
		)
	}
}

pub trait ConstructorVariableContextAttrs<'input>: LibSLParserContext<'input> + BorrowMut<ConstructorVariableContextExt<'input>>{

/// Retrieves first TerminalNode corresponding to token COLON
/// Returns `None` if there is no child corresponding to token COLON
fn COLON(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(COLON, 0)
}
fn variableKind(&self) -> Option<Rc<VariableKindContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}
fn ident(&self) -> Option<Rc<IdentContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}
fn typeExpr(&self) -> Option<Rc<TypeExprContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}
/// Retrieves first TerminalNode corresponding to token EQ
/// Returns `None` if there is no child corresponding to token EQ
fn EQ(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(EQ, 0)
}
fn annotation_all(&self) ->  Vec<Rc<AnnotationContextAll<'input>>> where Self:Sized{
	self.children_of_type()
}
fn annotation(&self, i: usize) -> Option<Rc<AnnotationContextAll<'input>>> where Self:Sized{
	self.child_of_type(i)
}
fn expr(&self) -> Option<Rc<ExprContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}

}

impl<'input> ConstructorVariableContextAttrs<'input> for ConstructorVariableContext<'input>{}

impl<'input, I, H> LibSLParser<'input, I, H>
where
    I: TokenStream<'input, TF = LocalTokenFactory<'input> > + TidAble<'input>,
    H: ErrorStrategy<'input,BaseParserType<'input,I>>
{
	pub fn constructorVariable(&mut self,)
	-> Result<Rc<ConstructorVariableContextAll<'input>>,ANTLRError> {
		let mut recog = self;
		let _parentctx = recog.ctx.take();
		let mut _localctx = ConstructorVariableContextExt::new(_parentctx.clone(), recog.base.get_state());
        recog.base.enter_rule(_localctx.clone(), 52, RULE_constructorVariable);
        let mut _localctx: Rc<ConstructorVariableContextAll> = _localctx;
		let mut _la: isize = -1;
		let result: Result<(), ANTLRError> = (|| {

			//recog.base.enter_outer_alt(_localctx.clone(), 1);
			recog.base.enter_outer_alt(None, 1);
			{
			recog.base.set_state(512);
			recog.err_handler.sync(&mut recog.base)?;
			_la = recog.base.input.la(1);
			while _la==AT {
				{
				{
				/*InvokeRule annotation*/
				recog.base.set_state(509);
				let tmp = recog.annotation()?;
				 cast_mut::<_,ConstructorVariableContext >(&mut _localctx).annotation = Some(tmp.clone());
				  

				let temp =  cast_mut::<_,ConstructorVariableContext >(&mut _localctx).annotation.clone().unwrap()
				 ;
				 cast_mut::<_,ConstructorVariableContext >(&mut _localctx).annotations.push(temp);
				  
				}
				}
				recog.base.set_state(514);
				recog.err_handler.sync(&mut recog.base)?;
				_la = recog.base.input.la(1);
			}
			/*InvokeRule variableKind*/
			recog.base.set_state(515);
			let tmp = recog.variableKind()?;
			 cast_mut::<_,ConstructorVariableContext >(&mut _localctx).kind = Some(tmp.clone());
			  

			/*InvokeRule ident*/
			recog.base.set_state(516);
			let tmp = recog.ident()?;
			 cast_mut::<_,ConstructorVariableContext >(&mut _localctx).name = Some(tmp.clone());
			  

			recog.base.set_state(517);
			recog.base.match_token(COLON,&mut recog.err_handler)?;

			/*InvokeRule typeExpr*/
			recog.base.set_state(518);
			let tmp = recog.typeExpr_rec(0)?;
			 cast_mut::<_,ConstructorVariableContext >(&mut _localctx).r#type = Some(tmp.clone());
			  

			recog.base.set_state(521);
			recog.err_handler.sync(&mut recog.base)?;
			_la = recog.base.input.la(1);
			if _la==EQ {
				{
				recog.base.set_state(519);
				recog.base.match_token(EQ,&mut recog.err_handler)?;

				/*InvokeRule expr*/
				recog.base.set_state(520);
				let tmp = recog.expr_rec(0)?;
				 cast_mut::<_,ConstructorVariableContext >(&mut _localctx).init = Some(tmp.clone());
				  

				}
			}

			}
			Ok(())
		})();
		match result {
		Ok(_)=>{},
        Err(e @ ANTLRError::FallThrough(_)) => return Err(e),
		Err(ref re) => {
				//_localctx.exception = re;
				recog.err_handler.report_error(&mut recog.base, re);
				recog.err_handler.recover(&mut recog.base, re)?;
			}
		}
		recog.base.exit_rule();

		Ok(_localctx)
	}
}
//------------------- implementedConcepts ----------------
pub type ImplementedConceptsContextAll<'input> = ImplementedConceptsContext<'input>;


pub type ImplementedConceptsContext<'input> = BaseParserRuleContext<'input,ImplementedConceptsContextExt<'input>>;

#[derive(Clone)]
pub struct ImplementedConceptsContextExt<'input>{
	pub ident: Option<Rc<IdentContextAll<'input>>>,
	pub concepts:Vec<Rc<IdentContextAll<'input>>>,
ph:PhantomData<&'input str>
}

impl<'input> LibSLParserContext<'input> for ImplementedConceptsContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for ImplementedConceptsContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_implementedConcepts(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_implementedConcepts(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for ImplementedConceptsContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_implementedConcepts }
	//fn type_rule_index() -> usize where Self: Sized { RULE_implementedConcepts }
}
antlr_rust::tid!{ImplementedConceptsContextExt<'a>}

impl<'input> ImplementedConceptsContextExt<'input>{
	fn new(parent: Option<Rc<dyn LibSLParserContext<'input> + 'input > >, invoking_state: isize) -> Rc<ImplementedConceptsContextAll<'input>> {
		Rc::new(
			BaseParserRuleContext::new_parser_ctx(parent, invoking_state,ImplementedConceptsContextExt{
				ident: None, 
				concepts: Vec::new(), 
				ph:PhantomData
			}),
		)
	}
}

pub trait ImplementedConceptsContextAttrs<'input>: LibSLParserContext<'input> + BorrowMut<ImplementedConceptsContextExt<'input>>{

/// Retrieves first TerminalNode corresponding to token IMPLEMENTS
/// Returns `None` if there is no child corresponding to token IMPLEMENTS
fn IMPLEMENTS(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(IMPLEMENTS, 0)
}
fn ident_all(&self) ->  Vec<Rc<IdentContextAll<'input>>> where Self:Sized{
	self.children_of_type()
}
fn ident(&self, i: usize) -> Option<Rc<IdentContextAll<'input>>> where Self:Sized{
	self.child_of_type(i)
}
/// Retrieves all `TerminalNode`s corresponding to token COMMA in current rule
fn COMMA_all(&self) -> Vec<Rc<TerminalNode<'input,LibSLParserContextType>>>  where Self:Sized{
	self.get_tokens(COMMA)
}
/// Retrieves 'i's TerminalNode corresponding to token COMMA, starting from 0.
/// Returns `None` if number of children corresponding to token COMMA is less or equal than `i`.
fn COMMA(&self, i: usize) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(COMMA, i)
}

}

impl<'input> ImplementedConceptsContextAttrs<'input> for ImplementedConceptsContext<'input>{}

impl<'input, I, H> LibSLParser<'input, I, H>
where
    I: TokenStream<'input, TF = LocalTokenFactory<'input> > + TidAble<'input>,
    H: ErrorStrategy<'input,BaseParserType<'input,I>>
{
	pub fn implementedConcepts(&mut self,)
	-> Result<Rc<ImplementedConceptsContextAll<'input>>,ANTLRError> {
		let mut recog = self;
		let _parentctx = recog.ctx.take();
		let mut _localctx = ImplementedConceptsContextExt::new(_parentctx.clone(), recog.base.get_state());
        recog.base.enter_rule(_localctx.clone(), 54, RULE_implementedConcepts);
        let mut _localctx: Rc<ImplementedConceptsContextAll> = _localctx;
		let result: Result<(), ANTLRError> = (|| {

			let mut _alt: isize;
			//recog.base.enter_outer_alt(_localctx.clone(), 1);
			recog.base.enter_outer_alt(None, 1);
			{
			recog.base.set_state(523);
			recog.base.match_token(IMPLEMENTS,&mut recog.err_handler)?;

			/*InvokeRule ident*/
			recog.base.set_state(524);
			let tmp = recog.ident()?;
			 cast_mut::<_,ImplementedConceptsContext >(&mut _localctx).ident = Some(tmp.clone());
			  

			let temp =  cast_mut::<_,ImplementedConceptsContext >(&mut _localctx).ident.clone().unwrap()
			 ;
			 cast_mut::<_,ImplementedConceptsContext >(&mut _localctx).concepts.push(temp);
			  
			recog.base.set_state(529);
			recog.err_handler.sync(&mut recog.base)?;
			_alt = recog.interpreter.adaptive_predict(48,&mut recog.base)?;
			while { _alt!=2 && _alt!=INVALID_ALT } {
				if _alt==1 {
					{
					{
					recog.base.set_state(525);
					recog.base.match_token(COMMA,&mut recog.err_handler)?;

					/*InvokeRule ident*/
					recog.base.set_state(526);
					let tmp = recog.ident()?;
					 cast_mut::<_,ImplementedConceptsContext >(&mut _localctx).ident = Some(tmp.clone());
					  

					let temp =  cast_mut::<_,ImplementedConceptsContext >(&mut _localctx).ident.clone().unwrap()
					 ;
					 cast_mut::<_,ImplementedConceptsContext >(&mut _localctx).concepts.push(temp);
					  
					}
					} 
				}
				recog.base.set_state(531);
				recog.err_handler.sync(&mut recog.base)?;
				_alt = recog.interpreter.adaptive_predict(48,&mut recog.base)?;
			}
			}
			Ok(())
		})();
		match result {
		Ok(_)=>{},
        Err(e @ ANTLRError::FallThrough(_)) => return Err(e),
		Err(ref re) => {
				//_localctx.exception = re;
				recog.err_handler.report_error(&mut recog.base, re);
				recog.err_handler.recover(&mut recog.base, re)?;
			}
		}
		recog.base.exit_rule();

		Ok(_localctx)
	}
}
//------------------- automatonDefDecl ----------------
#[derive(Debug)]
pub enum AutomatonDefDeclContextAll<'input>{
	AutomatonDefDeclProcContext(AutomatonDefDeclProcContext<'input>),
	AutomatonDefDeclConstructorContext(AutomatonDefDeclConstructorContext<'input>),
	AutomatonDefDeclShiftContext(AutomatonDefDeclShiftContext<'input>),
	AutomatonDefDeclPredContext(AutomatonDefDeclPredContext<'input>),
	AutomatonDefDeclVariableContext(AutomatonDefDeclVariableContext<'input>),
	AutomatonDefDeclStateContext(AutomatonDefDeclStateContext<'input>),
	AutomatonDefDeclDestructorContext(AutomatonDefDeclDestructorContext<'input>),
	AutomatonDefDeclFunctionContext(AutomatonDefDeclFunctionContext<'input>),
Error(AutomatonDefDeclContext<'input>)
}
antlr_rust::tid!{AutomatonDefDeclContextAll<'a>}

impl<'input> antlr_rust::parser_rule_context::DerefSeal for AutomatonDefDeclContextAll<'input>{}

impl<'input> LibSLParserContext<'input> for AutomatonDefDeclContextAll<'input>{}

impl<'input> Deref for AutomatonDefDeclContextAll<'input>{
	type Target = dyn AutomatonDefDeclContextAttrs<'input> + 'input;
	fn deref(&self) -> &Self::Target{
		use AutomatonDefDeclContextAll::*;
		match self{
			AutomatonDefDeclProcContext(inner) => inner,
			AutomatonDefDeclConstructorContext(inner) => inner,
			AutomatonDefDeclShiftContext(inner) => inner,
			AutomatonDefDeclPredContext(inner) => inner,
			AutomatonDefDeclVariableContext(inner) => inner,
			AutomatonDefDeclStateContext(inner) => inner,
			AutomatonDefDeclDestructorContext(inner) => inner,
			AutomatonDefDeclFunctionContext(inner) => inner,
Error(inner) => inner
		}
	}
}
impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for AutomatonDefDeclContextAll<'input>{
    fn enter(&self, listener: &mut (dyn LibSLParserListener<'input> + 'a)) { self.deref().enter(listener) }
    fn exit(&self, listener: &mut (dyn LibSLParserListener<'input> + 'a)) { self.deref().exit(listener) }
}



pub type AutomatonDefDeclContext<'input> = BaseParserRuleContext<'input,AutomatonDefDeclContextExt<'input>>;

#[derive(Clone)]
pub struct AutomatonDefDeclContextExt<'input>{
ph:PhantomData<&'input str>
}

impl<'input> LibSLParserContext<'input> for AutomatonDefDeclContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for AutomatonDefDeclContext<'input>{
}

impl<'input> CustomRuleContext<'input> for AutomatonDefDeclContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_automatonDefDecl }
	//fn type_rule_index() -> usize where Self: Sized { RULE_automatonDefDecl }
}
antlr_rust::tid!{AutomatonDefDeclContextExt<'a>}

impl<'input> AutomatonDefDeclContextExt<'input>{
	fn new(parent: Option<Rc<dyn LibSLParserContext<'input> + 'input > >, invoking_state: isize) -> Rc<AutomatonDefDeclContextAll<'input>> {
		Rc::new(
		AutomatonDefDeclContextAll::Error(
			BaseParserRuleContext::new_parser_ctx(parent, invoking_state,AutomatonDefDeclContextExt{
				ph:PhantomData
			}),
		)
		)
	}
}

pub trait AutomatonDefDeclContextAttrs<'input>: LibSLParserContext<'input> + BorrowMut<AutomatonDefDeclContextExt<'input>>{


}

impl<'input> AutomatonDefDeclContextAttrs<'input> for AutomatonDefDeclContext<'input>{}

pub type AutomatonDefDeclProcContext<'input> = BaseParserRuleContext<'input,AutomatonDefDeclProcContextExt<'input>>;

pub trait AutomatonDefDeclProcContextAttrs<'input>: LibSLParserContext<'input>{
	fn procDecl(&self) -> Option<Rc<ProcDeclContextAll<'input>>> where Self:Sized{
		self.child_of_type(0)
	}
}

impl<'input> AutomatonDefDeclProcContextAttrs<'input> for AutomatonDefDeclProcContext<'input>{}

pub struct AutomatonDefDeclProcContextExt<'input>{
	__base:AutomatonDefDeclContextExt<'input>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{AutomatonDefDeclProcContextExt<'a>}

impl<'input> LibSLParserContext<'input> for AutomatonDefDeclProcContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for AutomatonDefDeclProcContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_AutomatonDefDeclProc(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_AutomatonDefDeclProc(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for AutomatonDefDeclProcContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_automatonDefDecl }
	//fn type_rule_index() -> usize where Self: Sized { RULE_automatonDefDecl }
}

impl<'input> Borrow<AutomatonDefDeclContextExt<'input>> for AutomatonDefDeclProcContext<'input>{
	fn borrow(&self) -> &AutomatonDefDeclContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<AutomatonDefDeclContextExt<'input>> for AutomatonDefDeclProcContext<'input>{
	fn borrow_mut(&mut self) -> &mut AutomatonDefDeclContextExt<'input> { &mut self.__base }
}

impl<'input> AutomatonDefDeclContextAttrs<'input> for AutomatonDefDeclProcContext<'input> {}

impl<'input> AutomatonDefDeclProcContextExt<'input>{
	fn new(ctx: &dyn AutomatonDefDeclContextAttrs<'input>) -> Rc<AutomatonDefDeclContextAll<'input>>  {
		Rc::new(
			AutomatonDefDeclContextAll::AutomatonDefDeclProcContext(
				BaseParserRuleContext::copy_from(ctx,AutomatonDefDeclProcContextExt{
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type AutomatonDefDeclConstructorContext<'input> = BaseParserRuleContext<'input,AutomatonDefDeclConstructorContextExt<'input>>;

pub trait AutomatonDefDeclConstructorContextAttrs<'input>: LibSLParserContext<'input>{
	fn constructorDecl(&self) -> Option<Rc<ConstructorDeclContextAll<'input>>> where Self:Sized{
		self.child_of_type(0)
	}
}

impl<'input> AutomatonDefDeclConstructorContextAttrs<'input> for AutomatonDefDeclConstructorContext<'input>{}

pub struct AutomatonDefDeclConstructorContextExt<'input>{
	__base:AutomatonDefDeclContextExt<'input>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{AutomatonDefDeclConstructorContextExt<'a>}

impl<'input> LibSLParserContext<'input> for AutomatonDefDeclConstructorContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for AutomatonDefDeclConstructorContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_AutomatonDefDeclConstructor(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_AutomatonDefDeclConstructor(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for AutomatonDefDeclConstructorContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_automatonDefDecl }
	//fn type_rule_index() -> usize where Self: Sized { RULE_automatonDefDecl }
}

impl<'input> Borrow<AutomatonDefDeclContextExt<'input>> for AutomatonDefDeclConstructorContext<'input>{
	fn borrow(&self) -> &AutomatonDefDeclContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<AutomatonDefDeclContextExt<'input>> for AutomatonDefDeclConstructorContext<'input>{
	fn borrow_mut(&mut self) -> &mut AutomatonDefDeclContextExt<'input> { &mut self.__base }
}

impl<'input> AutomatonDefDeclContextAttrs<'input> for AutomatonDefDeclConstructorContext<'input> {}

impl<'input> AutomatonDefDeclConstructorContextExt<'input>{
	fn new(ctx: &dyn AutomatonDefDeclContextAttrs<'input>) -> Rc<AutomatonDefDeclContextAll<'input>>  {
		Rc::new(
			AutomatonDefDeclContextAll::AutomatonDefDeclConstructorContext(
				BaseParserRuleContext::copy_from(ctx,AutomatonDefDeclConstructorContextExt{
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type AutomatonDefDeclShiftContext<'input> = BaseParserRuleContext<'input,AutomatonDefDeclShiftContextExt<'input>>;

pub trait AutomatonDefDeclShiftContextAttrs<'input>: LibSLParserContext<'input>{
	fn shiftDecl(&self) -> Option<Rc<ShiftDeclContextAll<'input>>> where Self:Sized{
		self.child_of_type(0)
	}
}

impl<'input> AutomatonDefDeclShiftContextAttrs<'input> for AutomatonDefDeclShiftContext<'input>{}

pub struct AutomatonDefDeclShiftContextExt<'input>{
	__base:AutomatonDefDeclContextExt<'input>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{AutomatonDefDeclShiftContextExt<'a>}

impl<'input> LibSLParserContext<'input> for AutomatonDefDeclShiftContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for AutomatonDefDeclShiftContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_AutomatonDefDeclShift(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_AutomatonDefDeclShift(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for AutomatonDefDeclShiftContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_automatonDefDecl }
	//fn type_rule_index() -> usize where Self: Sized { RULE_automatonDefDecl }
}

impl<'input> Borrow<AutomatonDefDeclContextExt<'input>> for AutomatonDefDeclShiftContext<'input>{
	fn borrow(&self) -> &AutomatonDefDeclContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<AutomatonDefDeclContextExt<'input>> for AutomatonDefDeclShiftContext<'input>{
	fn borrow_mut(&mut self) -> &mut AutomatonDefDeclContextExt<'input> { &mut self.__base }
}

impl<'input> AutomatonDefDeclContextAttrs<'input> for AutomatonDefDeclShiftContext<'input> {}

impl<'input> AutomatonDefDeclShiftContextExt<'input>{
	fn new(ctx: &dyn AutomatonDefDeclContextAttrs<'input>) -> Rc<AutomatonDefDeclContextAll<'input>>  {
		Rc::new(
			AutomatonDefDeclContextAll::AutomatonDefDeclShiftContext(
				BaseParserRuleContext::copy_from(ctx,AutomatonDefDeclShiftContextExt{
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type AutomatonDefDeclPredContext<'input> = BaseParserRuleContext<'input,AutomatonDefDeclPredContextExt<'input>>;

pub trait AutomatonDefDeclPredContextAttrs<'input>: LibSLParserContext<'input>{
	fn predDecl(&self) -> Option<Rc<PredDeclContextAll<'input>>> where Self:Sized{
		self.child_of_type(0)
	}
}

impl<'input> AutomatonDefDeclPredContextAttrs<'input> for AutomatonDefDeclPredContext<'input>{}

pub struct AutomatonDefDeclPredContextExt<'input>{
	__base:AutomatonDefDeclContextExt<'input>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{AutomatonDefDeclPredContextExt<'a>}

impl<'input> LibSLParserContext<'input> for AutomatonDefDeclPredContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for AutomatonDefDeclPredContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_AutomatonDefDeclPred(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_AutomatonDefDeclPred(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for AutomatonDefDeclPredContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_automatonDefDecl }
	//fn type_rule_index() -> usize where Self: Sized { RULE_automatonDefDecl }
}

impl<'input> Borrow<AutomatonDefDeclContextExt<'input>> for AutomatonDefDeclPredContext<'input>{
	fn borrow(&self) -> &AutomatonDefDeclContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<AutomatonDefDeclContextExt<'input>> for AutomatonDefDeclPredContext<'input>{
	fn borrow_mut(&mut self) -> &mut AutomatonDefDeclContextExt<'input> { &mut self.__base }
}

impl<'input> AutomatonDefDeclContextAttrs<'input> for AutomatonDefDeclPredContext<'input> {}

impl<'input> AutomatonDefDeclPredContextExt<'input>{
	fn new(ctx: &dyn AutomatonDefDeclContextAttrs<'input>) -> Rc<AutomatonDefDeclContextAll<'input>>  {
		Rc::new(
			AutomatonDefDeclContextAll::AutomatonDefDeclPredContext(
				BaseParserRuleContext::copy_from(ctx,AutomatonDefDeclPredContextExt{
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type AutomatonDefDeclVariableContext<'input> = BaseParserRuleContext<'input,AutomatonDefDeclVariableContextExt<'input>>;

pub trait AutomatonDefDeclVariableContextAttrs<'input>: LibSLParserContext<'input>{
	fn variableDecl(&self) -> Option<Rc<VariableDeclContextAll<'input>>> where Self:Sized{
		self.child_of_type(0)
	}
}

impl<'input> AutomatonDefDeclVariableContextAttrs<'input> for AutomatonDefDeclVariableContext<'input>{}

pub struct AutomatonDefDeclVariableContextExt<'input>{
	__base:AutomatonDefDeclContextExt<'input>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{AutomatonDefDeclVariableContextExt<'a>}

impl<'input> LibSLParserContext<'input> for AutomatonDefDeclVariableContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for AutomatonDefDeclVariableContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_AutomatonDefDeclVariable(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_AutomatonDefDeclVariable(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for AutomatonDefDeclVariableContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_automatonDefDecl }
	//fn type_rule_index() -> usize where Self: Sized { RULE_automatonDefDecl }
}

impl<'input> Borrow<AutomatonDefDeclContextExt<'input>> for AutomatonDefDeclVariableContext<'input>{
	fn borrow(&self) -> &AutomatonDefDeclContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<AutomatonDefDeclContextExt<'input>> for AutomatonDefDeclVariableContext<'input>{
	fn borrow_mut(&mut self) -> &mut AutomatonDefDeclContextExt<'input> { &mut self.__base }
}

impl<'input> AutomatonDefDeclContextAttrs<'input> for AutomatonDefDeclVariableContext<'input> {}

impl<'input> AutomatonDefDeclVariableContextExt<'input>{
	fn new(ctx: &dyn AutomatonDefDeclContextAttrs<'input>) -> Rc<AutomatonDefDeclContextAll<'input>>  {
		Rc::new(
			AutomatonDefDeclContextAll::AutomatonDefDeclVariableContext(
				BaseParserRuleContext::copy_from(ctx,AutomatonDefDeclVariableContextExt{
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type AutomatonDefDeclStateContext<'input> = BaseParserRuleContext<'input,AutomatonDefDeclStateContextExt<'input>>;

pub trait AutomatonDefDeclStateContextAttrs<'input>: LibSLParserContext<'input>{
	fn stateDecl(&self) -> Option<Rc<StateDeclContextAll<'input>>> where Self:Sized{
		self.child_of_type(0)
	}
}

impl<'input> AutomatonDefDeclStateContextAttrs<'input> for AutomatonDefDeclStateContext<'input>{}

pub struct AutomatonDefDeclStateContextExt<'input>{
	__base:AutomatonDefDeclContextExt<'input>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{AutomatonDefDeclStateContextExt<'a>}

impl<'input> LibSLParserContext<'input> for AutomatonDefDeclStateContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for AutomatonDefDeclStateContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_AutomatonDefDeclState(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_AutomatonDefDeclState(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for AutomatonDefDeclStateContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_automatonDefDecl }
	//fn type_rule_index() -> usize where Self: Sized { RULE_automatonDefDecl }
}

impl<'input> Borrow<AutomatonDefDeclContextExt<'input>> for AutomatonDefDeclStateContext<'input>{
	fn borrow(&self) -> &AutomatonDefDeclContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<AutomatonDefDeclContextExt<'input>> for AutomatonDefDeclStateContext<'input>{
	fn borrow_mut(&mut self) -> &mut AutomatonDefDeclContextExt<'input> { &mut self.__base }
}

impl<'input> AutomatonDefDeclContextAttrs<'input> for AutomatonDefDeclStateContext<'input> {}

impl<'input> AutomatonDefDeclStateContextExt<'input>{
	fn new(ctx: &dyn AutomatonDefDeclContextAttrs<'input>) -> Rc<AutomatonDefDeclContextAll<'input>>  {
		Rc::new(
			AutomatonDefDeclContextAll::AutomatonDefDeclStateContext(
				BaseParserRuleContext::copy_from(ctx,AutomatonDefDeclStateContextExt{
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type AutomatonDefDeclDestructorContext<'input> = BaseParserRuleContext<'input,AutomatonDefDeclDestructorContextExt<'input>>;

pub trait AutomatonDefDeclDestructorContextAttrs<'input>: LibSLParserContext<'input>{
	fn destructorDecl(&self) -> Option<Rc<DestructorDeclContextAll<'input>>> where Self:Sized{
		self.child_of_type(0)
	}
}

impl<'input> AutomatonDefDeclDestructorContextAttrs<'input> for AutomatonDefDeclDestructorContext<'input>{}

pub struct AutomatonDefDeclDestructorContextExt<'input>{
	__base:AutomatonDefDeclContextExt<'input>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{AutomatonDefDeclDestructorContextExt<'a>}

impl<'input> LibSLParserContext<'input> for AutomatonDefDeclDestructorContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for AutomatonDefDeclDestructorContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_AutomatonDefDeclDestructor(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_AutomatonDefDeclDestructor(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for AutomatonDefDeclDestructorContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_automatonDefDecl }
	//fn type_rule_index() -> usize where Self: Sized { RULE_automatonDefDecl }
}

impl<'input> Borrow<AutomatonDefDeclContextExt<'input>> for AutomatonDefDeclDestructorContext<'input>{
	fn borrow(&self) -> &AutomatonDefDeclContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<AutomatonDefDeclContextExt<'input>> for AutomatonDefDeclDestructorContext<'input>{
	fn borrow_mut(&mut self) -> &mut AutomatonDefDeclContextExt<'input> { &mut self.__base }
}

impl<'input> AutomatonDefDeclContextAttrs<'input> for AutomatonDefDeclDestructorContext<'input> {}

impl<'input> AutomatonDefDeclDestructorContextExt<'input>{
	fn new(ctx: &dyn AutomatonDefDeclContextAttrs<'input>) -> Rc<AutomatonDefDeclContextAll<'input>>  {
		Rc::new(
			AutomatonDefDeclContextAll::AutomatonDefDeclDestructorContext(
				BaseParserRuleContext::copy_from(ctx,AutomatonDefDeclDestructorContextExt{
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type AutomatonDefDeclFunctionContext<'input> = BaseParserRuleContext<'input,AutomatonDefDeclFunctionContextExt<'input>>;

pub trait AutomatonDefDeclFunctionContextAttrs<'input>: LibSLParserContext<'input>{
	fn functionDecl(&self) -> Option<Rc<FunctionDeclContextAll<'input>>> where Self:Sized{
		self.child_of_type(0)
	}
}

impl<'input> AutomatonDefDeclFunctionContextAttrs<'input> for AutomatonDefDeclFunctionContext<'input>{}

pub struct AutomatonDefDeclFunctionContextExt<'input>{
	__base:AutomatonDefDeclContextExt<'input>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{AutomatonDefDeclFunctionContextExt<'a>}

impl<'input> LibSLParserContext<'input> for AutomatonDefDeclFunctionContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for AutomatonDefDeclFunctionContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_AutomatonDefDeclFunction(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_AutomatonDefDeclFunction(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for AutomatonDefDeclFunctionContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_automatonDefDecl }
	//fn type_rule_index() -> usize where Self: Sized { RULE_automatonDefDecl }
}

impl<'input> Borrow<AutomatonDefDeclContextExt<'input>> for AutomatonDefDeclFunctionContext<'input>{
	fn borrow(&self) -> &AutomatonDefDeclContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<AutomatonDefDeclContextExt<'input>> for AutomatonDefDeclFunctionContext<'input>{
	fn borrow_mut(&mut self) -> &mut AutomatonDefDeclContextExt<'input> { &mut self.__base }
}

impl<'input> AutomatonDefDeclContextAttrs<'input> for AutomatonDefDeclFunctionContext<'input> {}

impl<'input> AutomatonDefDeclFunctionContextExt<'input>{
	fn new(ctx: &dyn AutomatonDefDeclContextAttrs<'input>) -> Rc<AutomatonDefDeclContextAll<'input>>  {
		Rc::new(
			AutomatonDefDeclContextAll::AutomatonDefDeclFunctionContext(
				BaseParserRuleContext::copy_from(ctx,AutomatonDefDeclFunctionContextExt{
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

impl<'input, I, H> LibSLParser<'input, I, H>
where
    I: TokenStream<'input, TF = LocalTokenFactory<'input> > + TidAble<'input>,
    H: ErrorStrategy<'input,BaseParserType<'input,I>>
{
	pub fn automatonDefDecl(&mut self,)
	-> Result<Rc<AutomatonDefDeclContextAll<'input>>,ANTLRError> {
		let mut recog = self;
		let _parentctx = recog.ctx.take();
		let mut _localctx = AutomatonDefDeclContextExt::new(_parentctx.clone(), recog.base.get_state());
        recog.base.enter_rule(_localctx.clone(), 56, RULE_automatonDefDecl);
        let mut _localctx: Rc<AutomatonDefDeclContextAll> = _localctx;
		let result: Result<(), ANTLRError> = (|| {

			recog.base.set_state(540);
			recog.err_handler.sync(&mut recog.base)?;
			match  recog.interpreter.adaptive_predict(49,&mut recog.base)? {
				1 =>{
					let tmp = AutomatonDefDeclStateContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 1);
					_localctx = tmp;
					{
					/*InvokeRule stateDecl*/
					recog.base.set_state(532);
					recog.stateDecl()?;

					}
				}
			,
				2 =>{
					let tmp = AutomatonDefDeclShiftContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 2);
					_localctx = tmp;
					{
					/*InvokeRule shiftDecl*/
					recog.base.set_state(533);
					recog.shiftDecl()?;

					}
				}
			,
				3 =>{
					let tmp = AutomatonDefDeclConstructorContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 3);
					_localctx = tmp;
					{
					/*InvokeRule constructorDecl*/
					recog.base.set_state(534);
					recog.constructorDecl()?;

					}
				}
			,
				4 =>{
					let tmp = AutomatonDefDeclDestructorContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 4);
					_localctx = tmp;
					{
					/*InvokeRule destructorDecl*/
					recog.base.set_state(535);
					recog.destructorDecl()?;

					}
				}
			,
				5 =>{
					let tmp = AutomatonDefDeclProcContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 5);
					_localctx = tmp;
					{
					/*InvokeRule procDecl*/
					recog.base.set_state(536);
					recog.procDecl()?;

					}
				}
			,
				6 =>{
					let tmp = AutomatonDefDeclPredContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 6);
					_localctx = tmp;
					{
					/*InvokeRule predDecl*/
					recog.base.set_state(537);
					recog.predDecl()?;

					}
				}
			,
				7 =>{
					let tmp = AutomatonDefDeclFunctionContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 7);
					_localctx = tmp;
					{
					/*InvokeRule functionDecl*/
					recog.base.set_state(538);
					recog.functionDecl()?;

					}
				}
			,
				8 =>{
					let tmp = AutomatonDefDeclVariableContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 8);
					_localctx = tmp;
					{
					/*InvokeRule variableDecl*/
					recog.base.set_state(539);
					recog.variableDecl()?;

					}
				}

				_ => {}
			}
			Ok(())
		})();
		match result {
		Ok(_)=>{},
        Err(e @ ANTLRError::FallThrough(_)) => return Err(e),
		Err(ref re) => {
				//_localctx.exception = re;
				recog.err_handler.report_error(&mut recog.base, re);
				recog.err_handler.recover(&mut recog.base, re)?;
			}
		}
		recog.base.exit_rule();

		Ok(_localctx)
	}
}
//------------------- functionDecl ----------------
pub type FunctionDeclContextAll<'input> = FunctionDeclContext<'input>;


pub type FunctionDeclContext<'input> = BaseParserRuleContext<'input,FunctionDeclContextExt<'input>>;

#[derive(Clone)]
pub struct FunctionDeclContextExt<'input>{
	pub annotation: Option<Rc<AnnotationContextAll<'input>>>,
	pub annotations:Vec<Rc<AnnotationContextAll<'input>>>,
	pub functionModifier: Option<Rc<FunctionModifierContextAll<'input>>>,
	pub modifiers:Vec<Rc<FunctionModifierContextAll<'input>>>,
	pub extensionFor: Option<Rc<FullNameContextAll<'input>>>,
	pub method: Option<Rc<MethodSpecContextAll<'input>>>,
	pub name: Option<Rc<IdentContextAll<'input>>>,
	pub typeParams: Option<Rc<GenericsContextAll<'input>>>,
	pub params: Option<Rc<FunctionParamListContextAll<'input>>>,
	pub retType: Option<Rc<TypeExprContextAll<'input>>>,
	pub typeConstraints: Option<Rc<WhereClauseContextAll<'input>>>,
	pub def: Option<Rc<FunctionDefContextAll<'input>>>,
ph:PhantomData<&'input str>
}

impl<'input> LibSLParserContext<'input> for FunctionDeclContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for FunctionDeclContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_functionDecl(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_functionDecl(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for FunctionDeclContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_functionDecl }
	//fn type_rule_index() -> usize where Self: Sized { RULE_functionDecl }
}
antlr_rust::tid!{FunctionDeclContextExt<'a>}

impl<'input> FunctionDeclContextExt<'input>{
	fn new(parent: Option<Rc<dyn LibSLParserContext<'input> + 'input > >, invoking_state: isize) -> Rc<FunctionDeclContextAll<'input>> {
		Rc::new(
			BaseParserRuleContext::new_parser_ctx(parent, invoking_state,FunctionDeclContextExt{
				annotation: None, functionModifier: None, extensionFor: None, method: None, name: None, typeParams: None, params: None, retType: None, typeConstraints: None, def: None, 
				annotations: Vec::new(), modifiers: Vec::new(), 
				ph:PhantomData
			}),
		)
	}
}

pub trait FunctionDeclContextAttrs<'input>: LibSLParserContext<'input> + BorrowMut<FunctionDeclContextExt<'input>>{

/// Retrieves first TerminalNode corresponding to token FUN
/// Returns `None` if there is no child corresponding to token FUN
fn FUN(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(FUN, 0)
}
/// Retrieves first TerminalNode corresponding to token L_PAREN
/// Returns `None` if there is no child corresponding to token L_PAREN
fn L_PAREN(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(L_PAREN, 0)
}
/// Retrieves first TerminalNode corresponding to token R_PAREN
/// Returns `None` if there is no child corresponding to token R_PAREN
fn R_PAREN(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(R_PAREN, 0)
}
fn ident(&self) -> Option<Rc<IdentContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}
fn functionDef(&self) -> Option<Rc<FunctionDefContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}
/// Retrieves first TerminalNode corresponding to token DOT
/// Returns `None` if there is no child corresponding to token DOT
fn DOT(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(DOT, 0)
}
/// Retrieves first TerminalNode corresponding to token COLON
/// Returns `None` if there is no child corresponding to token COLON
fn COLON(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(COLON, 0)
}
fn annotation_all(&self) ->  Vec<Rc<AnnotationContextAll<'input>>> where Self:Sized{
	self.children_of_type()
}
fn annotation(&self, i: usize) -> Option<Rc<AnnotationContextAll<'input>>> where Self:Sized{
	self.child_of_type(i)
}
fn functionModifier_all(&self) ->  Vec<Rc<FunctionModifierContextAll<'input>>> where Self:Sized{
	self.children_of_type()
}
fn functionModifier(&self, i: usize) -> Option<Rc<FunctionModifierContextAll<'input>>> where Self:Sized{
	self.child_of_type(i)
}
fn fullName(&self) -> Option<Rc<FullNameContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}
fn methodSpec(&self) -> Option<Rc<MethodSpecContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}
fn generics(&self) -> Option<Rc<GenericsContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}
fn functionParamList(&self) -> Option<Rc<FunctionParamListContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}
fn typeExpr(&self) -> Option<Rc<TypeExprContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}
fn whereClause(&self) -> Option<Rc<WhereClauseContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}
/// Retrieves first TerminalNode corresponding to token COMMA
/// Returns `None` if there is no child corresponding to token COMMA
fn COMMA(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(COMMA, 0)
}

}

impl<'input> FunctionDeclContextAttrs<'input> for FunctionDeclContext<'input>{}

impl<'input, I, H> LibSLParser<'input, I, H>
where
    I: TokenStream<'input, TF = LocalTokenFactory<'input> > + TidAble<'input>,
    H: ErrorStrategy<'input,BaseParserType<'input,I>>
{
	pub fn functionDecl(&mut self,)
	-> Result<Rc<FunctionDeclContextAll<'input>>,ANTLRError> {
		let mut recog = self;
		let _parentctx = recog.ctx.take();
		let mut _localctx = FunctionDeclContextExt::new(_parentctx.clone(), recog.base.get_state());
        recog.base.enter_rule(_localctx.clone(), 58, RULE_functionDecl);
        let mut _localctx: Rc<FunctionDeclContextAll> = _localctx;
		let mut _la: isize = -1;
		let result: Result<(), ANTLRError> = (|| {

			//recog.base.enter_outer_alt(_localctx.clone(), 1);
			recog.base.enter_outer_alt(None, 1);
			{
			recog.base.set_state(545);
			recog.err_handler.sync(&mut recog.base)?;
			_la = recog.base.input.la(1);
			while _la==AT {
				{
				{
				/*InvokeRule annotation*/
				recog.base.set_state(542);
				let tmp = recog.annotation()?;
				 cast_mut::<_,FunctionDeclContext >(&mut _localctx).annotation = Some(tmp.clone());
				  

				let temp =  cast_mut::<_,FunctionDeclContext >(&mut _localctx).annotation.clone().unwrap()
				 ;
				 cast_mut::<_,FunctionDeclContext >(&mut _localctx).annotations.push(temp);
				  
				}
				}
				recog.base.set_state(547);
				recog.err_handler.sync(&mut recog.base)?;
				_la = recog.base.input.la(1);
			}
			recog.base.set_state(551);
			recog.err_handler.sync(&mut recog.base)?;
			_la = recog.base.input.la(1);
			while _la==STATIC {
				{
				{
				/*InvokeRule functionModifier*/
				recog.base.set_state(548);
				let tmp = recog.functionModifier()?;
				 cast_mut::<_,FunctionDeclContext >(&mut _localctx).functionModifier = Some(tmp.clone());
				  

				let temp =  cast_mut::<_,FunctionDeclContext >(&mut _localctx).functionModifier.clone().unwrap()
				 ;
				 cast_mut::<_,FunctionDeclContext >(&mut _localctx).modifiers.push(temp);
				  
				}
				}
				recog.base.set_state(553);
				recog.err_handler.sync(&mut recog.base)?;
				_la = recog.base.input.la(1);
			}
			recog.base.set_state(554);
			recog.base.match_token(FUN,&mut recog.err_handler)?;

			recog.base.set_state(558);
			recog.err_handler.sync(&mut recog.base)?;
			match  recog.interpreter.adaptive_predict(52,&mut recog.base)? {
				x if x == 1=>{
					{
					/*InvokeRule fullName*/
					recog.base.set_state(555);
					let tmp = recog.fullName()?;
					 cast_mut::<_,FunctionDeclContext >(&mut _localctx).extensionFor = Some(tmp.clone());
					  

					recog.base.set_state(556);
					recog.base.match_token(DOT,&mut recog.err_handler)?;

					}
				}

				_ => {}
			}
			recog.base.set_state(561);
			recog.err_handler.sync(&mut recog.base)?;
			_la = recog.base.input.la(1);
			if _la==ASTERISK {
				{
				/*InvokeRule methodSpec*/
				recog.base.set_state(560);
				let tmp = recog.methodSpec()?;
				 cast_mut::<_,FunctionDeclContext >(&mut _localctx).method = Some(tmp.clone());
				  

				}
			}

			/*InvokeRule ident*/
			recog.base.set_state(563);
			let tmp = recog.ident()?;
			 cast_mut::<_,FunctionDeclContext >(&mut _localctx).name = Some(tmp.clone());
			  

			recog.base.set_state(565);
			recog.err_handler.sync(&mut recog.base)?;
			_la = recog.base.input.la(1);
			if _la==L_ANGLE {
				{
				/*InvokeRule generics*/
				recog.base.set_state(564);
				let tmp = recog.generics()?;
				 cast_mut::<_,FunctionDeclContext >(&mut _localctx).typeParams = Some(tmp.clone());
				  

				}
			}

			recog.base.set_state(567);
			recog.base.match_token(L_PAREN,&mut recog.err_handler)?;

			recog.base.set_state(572);
			recog.err_handler.sync(&mut recog.base)?;
			_la = recog.base.input.la(1);
			if ((((_la - 86)) & !0x3f) == 0 && ((1usize << (_la - 86)) & 647) != 0) {
				{
				/*InvokeRule functionParamList*/
				recog.base.set_state(568);
				let tmp = recog.functionParamList()?;
				 cast_mut::<_,FunctionDeclContext >(&mut _localctx).params = Some(tmp.clone());
				  

				recog.base.set_state(570);
				recog.err_handler.sync(&mut recog.base)?;
				_la = recog.base.input.la(1);
				if _la==COMMA {
					{
					recog.base.set_state(569);
					recog.base.match_token(COMMA,&mut recog.err_handler)?;

					}
				}

				}
			}

			recog.base.set_state(574);
			recog.base.match_token(R_PAREN,&mut recog.err_handler)?;

			recog.base.set_state(577);
			recog.err_handler.sync(&mut recog.base)?;
			_la = recog.base.input.la(1);
			if _la==COLON {
				{
				recog.base.set_state(575);
				recog.base.match_token(COLON,&mut recog.err_handler)?;

				/*InvokeRule typeExpr*/
				recog.base.set_state(576);
				let tmp = recog.typeExpr_rec(0)?;
				 cast_mut::<_,FunctionDeclContext >(&mut _localctx).retType = Some(tmp.clone());
				  

				}
			}

			recog.base.set_state(580);
			recog.err_handler.sync(&mut recog.base)?;
			_la = recog.base.input.la(1);
			if _la==WHERE {
				{
				/*InvokeRule whereClause*/
				recog.base.set_state(579);
				let tmp = recog.whereClause()?;
				 cast_mut::<_,FunctionDeclContext >(&mut _localctx).typeConstraints = Some(tmp.clone());
				  

				}
			}

			/*InvokeRule functionDef*/
			recog.base.set_state(582);
			let tmp = recog.functionDef()?;
			 cast_mut::<_,FunctionDeclContext >(&mut _localctx).def = Some(tmp.clone());
			  

			}
			Ok(())
		})();
		match result {
		Ok(_)=>{},
        Err(e @ ANTLRError::FallThrough(_)) => return Err(e),
		Err(ref re) => {
				//_localctx.exception = re;
				recog.err_handler.report_error(&mut recog.base, re);
				recog.err_handler.recover(&mut recog.base, re)?;
			}
		}
		recog.base.exit_rule();

		Ok(_localctx)
	}
}
//------------------- functionModifier ----------------
#[derive(Debug)]
pub enum FunctionModifierContextAll<'input>{
	FunctionModifierStaticContext(FunctionModifierStaticContext<'input>),
Error(FunctionModifierContext<'input>)
}
antlr_rust::tid!{FunctionModifierContextAll<'a>}

impl<'input> antlr_rust::parser_rule_context::DerefSeal for FunctionModifierContextAll<'input>{}

impl<'input> LibSLParserContext<'input> for FunctionModifierContextAll<'input>{}

impl<'input> Deref for FunctionModifierContextAll<'input>{
	type Target = dyn FunctionModifierContextAttrs<'input> + 'input;
	fn deref(&self) -> &Self::Target{
		use FunctionModifierContextAll::*;
		match self{
			FunctionModifierStaticContext(inner) => inner,
Error(inner) => inner
		}
	}
}
impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for FunctionModifierContextAll<'input>{
    fn enter(&self, listener: &mut (dyn LibSLParserListener<'input> + 'a)) { self.deref().enter(listener) }
    fn exit(&self, listener: &mut (dyn LibSLParserListener<'input> + 'a)) { self.deref().exit(listener) }
}



pub type FunctionModifierContext<'input> = BaseParserRuleContext<'input,FunctionModifierContextExt<'input>>;

#[derive(Clone)]
pub struct FunctionModifierContextExt<'input>{
ph:PhantomData<&'input str>
}

impl<'input> LibSLParserContext<'input> for FunctionModifierContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for FunctionModifierContext<'input>{
}

impl<'input> CustomRuleContext<'input> for FunctionModifierContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_functionModifier }
	//fn type_rule_index() -> usize where Self: Sized { RULE_functionModifier }
}
antlr_rust::tid!{FunctionModifierContextExt<'a>}

impl<'input> FunctionModifierContextExt<'input>{
	fn new(parent: Option<Rc<dyn LibSLParserContext<'input> + 'input > >, invoking_state: isize) -> Rc<FunctionModifierContextAll<'input>> {
		Rc::new(
		FunctionModifierContextAll::Error(
			BaseParserRuleContext::new_parser_ctx(parent, invoking_state,FunctionModifierContextExt{
				ph:PhantomData
			}),
		)
		)
	}
}

pub trait FunctionModifierContextAttrs<'input>: LibSLParserContext<'input> + BorrowMut<FunctionModifierContextExt<'input>>{


}

impl<'input> FunctionModifierContextAttrs<'input> for FunctionModifierContext<'input>{}

pub type FunctionModifierStaticContext<'input> = BaseParserRuleContext<'input,FunctionModifierStaticContextExt<'input>>;

pub trait FunctionModifierStaticContextAttrs<'input>: LibSLParserContext<'input>{
	/// Retrieves first TerminalNode corresponding to token STATIC
	/// Returns `None` if there is no child corresponding to token STATIC
	fn STATIC(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(STATIC, 0)
	}
}

impl<'input> FunctionModifierStaticContextAttrs<'input> for FunctionModifierStaticContext<'input>{}

pub struct FunctionModifierStaticContextExt<'input>{
	__base:FunctionModifierContextExt<'input>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{FunctionModifierStaticContextExt<'a>}

impl<'input> LibSLParserContext<'input> for FunctionModifierStaticContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for FunctionModifierStaticContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_FunctionModifierStatic(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_FunctionModifierStatic(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for FunctionModifierStaticContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_functionModifier }
	//fn type_rule_index() -> usize where Self: Sized { RULE_functionModifier }
}

impl<'input> Borrow<FunctionModifierContextExt<'input>> for FunctionModifierStaticContext<'input>{
	fn borrow(&self) -> &FunctionModifierContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<FunctionModifierContextExt<'input>> for FunctionModifierStaticContext<'input>{
	fn borrow_mut(&mut self) -> &mut FunctionModifierContextExt<'input> { &mut self.__base }
}

impl<'input> FunctionModifierContextAttrs<'input> for FunctionModifierStaticContext<'input> {}

impl<'input> FunctionModifierStaticContextExt<'input>{
	fn new(ctx: &dyn FunctionModifierContextAttrs<'input>) -> Rc<FunctionModifierContextAll<'input>>  {
		Rc::new(
			FunctionModifierContextAll::FunctionModifierStaticContext(
				BaseParserRuleContext::copy_from(ctx,FunctionModifierStaticContextExt{
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

impl<'input, I, H> LibSLParser<'input, I, H>
where
    I: TokenStream<'input, TF = LocalTokenFactory<'input> > + TidAble<'input>,
    H: ErrorStrategy<'input,BaseParserType<'input,I>>
{
	pub fn functionModifier(&mut self,)
	-> Result<Rc<FunctionModifierContextAll<'input>>,ANTLRError> {
		let mut recog = self;
		let _parentctx = recog.ctx.take();
		let mut _localctx = FunctionModifierContextExt::new(_parentctx.clone(), recog.base.get_state());
        recog.base.enter_rule(_localctx.clone(), 60, RULE_functionModifier);
        let mut _localctx: Rc<FunctionModifierContextAll> = _localctx;
		let result: Result<(), ANTLRError> = (|| {

			let tmp = FunctionModifierStaticContextExt::new(&**_localctx);
			recog.base.enter_outer_alt(Some(tmp.clone()), 1);
			_localctx = tmp;
			{
			recog.base.set_state(584);
			recog.base.match_token(STATIC,&mut recog.err_handler)?;

			}
			Ok(())
		})();
		match result {
		Ok(_)=>{},
        Err(e @ ANTLRError::FallThrough(_)) => return Err(e),
		Err(ref re) => {
				//_localctx.exception = re;
				recog.err_handler.report_error(&mut recog.base, re);
				recog.err_handler.recover(&mut recog.base, re)?;
			}
		}
		recog.base.exit_rule();

		Ok(_localctx)
	}
}
//------------------- methodSpec ----------------
pub type MethodSpecContextAll<'input> = MethodSpecContext<'input>;


pub type MethodSpecContext<'input> = BaseParserRuleContext<'input,MethodSpecContextExt<'input>>;

#[derive(Clone)]
pub struct MethodSpecContextExt<'input>{
ph:PhantomData<&'input str>
}

impl<'input> LibSLParserContext<'input> for MethodSpecContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for MethodSpecContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_methodSpec(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_methodSpec(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for MethodSpecContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_methodSpec }
	//fn type_rule_index() -> usize where Self: Sized { RULE_methodSpec }
}
antlr_rust::tid!{MethodSpecContextExt<'a>}

impl<'input> MethodSpecContextExt<'input>{
	fn new(parent: Option<Rc<dyn LibSLParserContext<'input> + 'input > >, invoking_state: isize) -> Rc<MethodSpecContextAll<'input>> {
		Rc::new(
			BaseParserRuleContext::new_parser_ctx(parent, invoking_state,MethodSpecContextExt{
				ph:PhantomData
			}),
		)
	}
}

pub trait MethodSpecContextAttrs<'input>: LibSLParserContext<'input> + BorrowMut<MethodSpecContextExt<'input>>{

/// Retrieves first TerminalNode corresponding to token ASTERISK
/// Returns `None` if there is no child corresponding to token ASTERISK
fn ASTERISK(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(ASTERISK, 0)
}
/// Retrieves first TerminalNode corresponding to token DOT
/// Returns `None` if there is no child corresponding to token DOT
fn DOT(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(DOT, 0)
}

}

impl<'input> MethodSpecContextAttrs<'input> for MethodSpecContext<'input>{}

impl<'input, I, H> LibSLParser<'input, I, H>
where
    I: TokenStream<'input, TF = LocalTokenFactory<'input> > + TidAble<'input>,
    H: ErrorStrategy<'input,BaseParserType<'input,I>>
{
	pub fn methodSpec(&mut self,)
	-> Result<Rc<MethodSpecContextAll<'input>>,ANTLRError> {
		let mut recog = self;
		let _parentctx = recog.ctx.take();
		let mut _localctx = MethodSpecContextExt::new(_parentctx.clone(), recog.base.get_state());
        recog.base.enter_rule(_localctx.clone(), 62, RULE_methodSpec);
        let mut _localctx: Rc<MethodSpecContextAll> = _localctx;
		let result: Result<(), ANTLRError> = (|| {

			//recog.base.enter_outer_alt(_localctx.clone(), 1);
			recog.base.enter_outer_alt(None, 1);
			{
			recog.base.set_state(586);
			recog.base.match_token(ASTERISK,&mut recog.err_handler)?;

			recog.base.set_state(587);
			recog.base.match_token(DOT,&mut recog.err_handler)?;

			}
			Ok(())
		})();
		match result {
		Ok(_)=>{},
        Err(e @ ANTLRError::FallThrough(_)) => return Err(e),
		Err(ref re) => {
				//_localctx.exception = re;
				recog.err_handler.report_error(&mut recog.base, re);
				recog.err_handler.recover(&mut recog.base, re)?;
			}
		}
		recog.base.exit_rule();

		Ok(_localctx)
	}
}
//------------------- functionDef ----------------
#[derive(Debug)]
pub enum FunctionDefContextAll<'input>{
	FunctionDefSemicolonContext(FunctionDefSemicolonContext<'input>),
	FunctionDefBracedContext(FunctionDefBracedContext<'input>),
Error(FunctionDefContext<'input>)
}
antlr_rust::tid!{FunctionDefContextAll<'a>}

impl<'input> antlr_rust::parser_rule_context::DerefSeal for FunctionDefContextAll<'input>{}

impl<'input> LibSLParserContext<'input> for FunctionDefContextAll<'input>{}

impl<'input> Deref for FunctionDefContextAll<'input>{
	type Target = dyn FunctionDefContextAttrs<'input> + 'input;
	fn deref(&self) -> &Self::Target{
		use FunctionDefContextAll::*;
		match self{
			FunctionDefSemicolonContext(inner) => inner,
			FunctionDefBracedContext(inner) => inner,
Error(inner) => inner
		}
	}
}
impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for FunctionDefContextAll<'input>{
    fn enter(&self, listener: &mut (dyn LibSLParserListener<'input> + 'a)) { self.deref().enter(listener) }
    fn exit(&self, listener: &mut (dyn LibSLParserListener<'input> + 'a)) { self.deref().exit(listener) }
}



pub type FunctionDefContext<'input> = BaseParserRuleContext<'input,FunctionDefContextExt<'input>>;

#[derive(Clone)]
pub struct FunctionDefContextExt<'input>{
ph:PhantomData<&'input str>
}

impl<'input> LibSLParserContext<'input> for FunctionDefContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for FunctionDefContext<'input>{
}

impl<'input> CustomRuleContext<'input> for FunctionDefContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_functionDef }
	//fn type_rule_index() -> usize where Self: Sized { RULE_functionDef }
}
antlr_rust::tid!{FunctionDefContextExt<'a>}

impl<'input> FunctionDefContextExt<'input>{
	fn new(parent: Option<Rc<dyn LibSLParserContext<'input> + 'input > >, invoking_state: isize) -> Rc<FunctionDefContextAll<'input>> {
		Rc::new(
		FunctionDefContextAll::Error(
			BaseParserRuleContext::new_parser_ctx(parent, invoking_state,FunctionDefContextExt{
				ph:PhantomData
			}),
		)
		)
	}
}

pub trait FunctionDefContextAttrs<'input>: LibSLParserContext<'input> + BorrowMut<FunctionDefContextExt<'input>>{


}

impl<'input> FunctionDefContextAttrs<'input> for FunctionDefContext<'input>{}

pub type FunctionDefSemicolonContext<'input> = BaseParserRuleContext<'input,FunctionDefSemicolonContextExt<'input>>;

pub trait FunctionDefSemicolonContextAttrs<'input>: LibSLParserContext<'input>{
	/// Retrieves first TerminalNode corresponding to token SEMICOLON
	/// Returns `None` if there is no child corresponding to token SEMICOLON
	fn SEMICOLON(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(SEMICOLON, 0)
	}
}

impl<'input> FunctionDefSemicolonContextAttrs<'input> for FunctionDefSemicolonContext<'input>{}

pub struct FunctionDefSemicolonContextExt<'input>{
	__base:FunctionDefContextExt<'input>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{FunctionDefSemicolonContextExt<'a>}

impl<'input> LibSLParserContext<'input> for FunctionDefSemicolonContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for FunctionDefSemicolonContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_FunctionDefSemicolon(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_FunctionDefSemicolon(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for FunctionDefSemicolonContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_functionDef }
	//fn type_rule_index() -> usize where Self: Sized { RULE_functionDef }
}

impl<'input> Borrow<FunctionDefContextExt<'input>> for FunctionDefSemicolonContext<'input>{
	fn borrow(&self) -> &FunctionDefContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<FunctionDefContextExt<'input>> for FunctionDefSemicolonContext<'input>{
	fn borrow_mut(&mut self) -> &mut FunctionDefContextExt<'input> { &mut self.__base }
}

impl<'input> FunctionDefContextAttrs<'input> for FunctionDefSemicolonContext<'input> {}

impl<'input> FunctionDefSemicolonContextExt<'input>{
	fn new(ctx: &dyn FunctionDefContextAttrs<'input>) -> Rc<FunctionDefContextAll<'input>>  {
		Rc::new(
			FunctionDefContextAll::FunctionDefSemicolonContext(
				BaseParserRuleContext::copy_from(ctx,FunctionDefSemicolonContextExt{
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type FunctionDefBracedContext<'input> = BaseParserRuleContext<'input,FunctionDefBracedContextExt<'input>>;

pub trait FunctionDefBracedContextAttrs<'input>: LibSLParserContext<'input>{
	/// Retrieves first TerminalNode corresponding to token L_BRACE
	/// Returns `None` if there is no child corresponding to token L_BRACE
	fn L_BRACE(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(L_BRACE, 0)
	}
	/// Retrieves first TerminalNode corresponding to token R_BRACE
	/// Returns `None` if there is no child corresponding to token R_BRACE
	fn R_BRACE(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(R_BRACE, 0)
	}
	fn functionBody(&self) -> Option<Rc<FunctionBodyContextAll<'input>>> where Self:Sized{
		self.child_of_type(0)
	}
}

impl<'input> FunctionDefBracedContextAttrs<'input> for FunctionDefBracedContext<'input>{}

pub struct FunctionDefBracedContextExt<'input>{
	__base:FunctionDefContextExt<'input>,
	pub body: Option<Rc<FunctionBodyContextAll<'input>>>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{FunctionDefBracedContextExt<'a>}

impl<'input> LibSLParserContext<'input> for FunctionDefBracedContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for FunctionDefBracedContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_FunctionDefBraced(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_FunctionDefBraced(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for FunctionDefBracedContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_functionDef }
	//fn type_rule_index() -> usize where Self: Sized { RULE_functionDef }
}

impl<'input> Borrow<FunctionDefContextExt<'input>> for FunctionDefBracedContext<'input>{
	fn borrow(&self) -> &FunctionDefContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<FunctionDefContextExt<'input>> for FunctionDefBracedContext<'input>{
	fn borrow_mut(&mut self) -> &mut FunctionDefContextExt<'input> { &mut self.__base }
}

impl<'input> FunctionDefContextAttrs<'input> for FunctionDefBracedContext<'input> {}

impl<'input> FunctionDefBracedContextExt<'input>{
	fn new(ctx: &dyn FunctionDefContextAttrs<'input>) -> Rc<FunctionDefContextAll<'input>>  {
		Rc::new(
			FunctionDefContextAll::FunctionDefBracedContext(
				BaseParserRuleContext::copy_from(ctx,FunctionDefBracedContextExt{
        			body:None, 
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

impl<'input, I, H> LibSLParser<'input, I, H>
where
    I: TokenStream<'input, TF = LocalTokenFactory<'input> > + TidAble<'input>,
    H: ErrorStrategy<'input,BaseParserType<'input,I>>
{
	pub fn functionDef(&mut self,)
	-> Result<Rc<FunctionDefContextAll<'input>>,ANTLRError> {
		let mut recog = self;
		let _parentctx = recog.ctx.take();
		let mut _localctx = FunctionDefContextExt::new(_parentctx.clone(), recog.base.get_state());
        recog.base.enter_rule(_localctx.clone(), 64, RULE_functionDef);
        let mut _localctx: Rc<FunctionDefContextAll> = _localctx;
		let mut _la: isize = -1;
		let result: Result<(), ANTLRError> = (|| {

			recog.base.set_state(596);
			recog.err_handler.sync(&mut recog.base)?;
			match recog.base.input.la(1) {
			 L_BRACE 
				=> {
					let tmp = FunctionDefBracedContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 1);
					_localctx = tmp;
					{
					recog.base.set_state(589);
					recog.base.match_token(L_BRACE,&mut recog.err_handler)?;

					/*InvokeRule functionBody*/
					recog.base.set_state(590);
					let tmp = recog.functionBody()?;
					if let FunctionDefContextAll::FunctionDefBracedContext(ctx) = cast_mut::<_,FunctionDefContextAll >(&mut _localctx){
					ctx.body = Some(tmp.clone()); } else {unreachable!("cant cast");}  

					recog.base.set_state(591);
					recog.base.match_token(R_BRACE,&mut recog.err_handler)?;

					}
				}

			 EOF | SEMICOLON | R_BRACE | IMPORT | INCLUDE | TYPEALIAS | TYPE | TYPES |
			 ENUM | ANNOTATION | AUTOMATON | VAR | VAL | INITSTATE | STATE | FINISHSTATE |
			 SHIFT | FUN | CONSTRUCTOR | DESTRUCTOR | PROC | PRED | DEFINE | STATIC |
			 PURE | AT 
				=> {
					let tmp = FunctionDefSemicolonContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 2);
					_localctx = tmp;
					{
					recog.base.set_state(594);
					recog.err_handler.sync(&mut recog.base)?;
					_la = recog.base.input.la(1);
					if _la==SEMICOLON {
						{
						recog.base.set_state(593);
						recog.base.match_token(SEMICOLON,&mut recog.err_handler)?;

						}
					}

					}
				}

				_ => Err(ANTLRError::NoAltError(NoViableAltError::new(&mut recog.base)))?
			}
			Ok(())
		})();
		match result {
		Ok(_)=>{},
        Err(e @ ANTLRError::FallThrough(_)) => return Err(e),
		Err(ref re) => {
				//_localctx.exception = re;
				recog.err_handler.report_error(&mut recog.base, re);
				recog.err_handler.recover(&mut recog.base, re)?;
			}
		}
		recog.base.exit_rule();

		Ok(_localctx)
	}
}
//------------------- predDecl ----------------
pub type PredDeclContextAll<'input> = PredDeclContext<'input>;


pub type PredDeclContext<'input> = BaseParserRuleContext<'input,PredDeclContextExt<'input>>;

#[derive(Clone)]
pub struct PredDeclContextExt<'input>{
	pub annotation: Option<Rc<AnnotationContextAll<'input>>>,
	pub annotations:Vec<Rc<AnnotationContextAll<'input>>>,
	pub name: Option<Rc<IdentContextAll<'input>>>,
	pub typeParams: Option<Rc<GenericsContextAll<'input>>>,
	pub params: Option<Rc<FunctionParamListContextAll<'input>>>,
	pub typeConstraints: Option<Rc<WhereClauseContextAll<'input>>>,
	pub def: Option<Rc<BlockPredicateContextAll<'input>>>,
ph:PhantomData<&'input str>
}

impl<'input> LibSLParserContext<'input> for PredDeclContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for PredDeclContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_predDecl(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_predDecl(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for PredDeclContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_predDecl }
	//fn type_rule_index() -> usize where Self: Sized { RULE_predDecl }
}
antlr_rust::tid!{PredDeclContextExt<'a>}

impl<'input> PredDeclContextExt<'input>{
	fn new(parent: Option<Rc<dyn LibSLParserContext<'input> + 'input > >, invoking_state: isize) -> Rc<PredDeclContextAll<'input>> {
		Rc::new(
			BaseParserRuleContext::new_parser_ctx(parent, invoking_state,PredDeclContextExt{
				annotation: None, name: None, typeParams: None, params: None, typeConstraints: None, def: None, 
				annotations: Vec::new(), 
				ph:PhantomData
			}),
		)
	}
}

pub trait PredDeclContextAttrs<'input>: LibSLParserContext<'input> + BorrowMut<PredDeclContextExt<'input>>{

/// Retrieves first TerminalNode corresponding to token PRED
/// Returns `None` if there is no child corresponding to token PRED
fn PRED(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(PRED, 0)
}
/// Retrieves first TerminalNode corresponding to token L_PAREN
/// Returns `None` if there is no child corresponding to token L_PAREN
fn L_PAREN(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(L_PAREN, 0)
}
/// Retrieves first TerminalNode corresponding to token R_PAREN
/// Returns `None` if there is no child corresponding to token R_PAREN
fn R_PAREN(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(R_PAREN, 0)
}
fn ident(&self) -> Option<Rc<IdentContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}
fn annotation_all(&self) ->  Vec<Rc<AnnotationContextAll<'input>>> where Self:Sized{
	self.children_of_type()
}
fn annotation(&self, i: usize) -> Option<Rc<AnnotationContextAll<'input>>> where Self:Sized{
	self.child_of_type(i)
}
fn generics(&self) -> Option<Rc<GenericsContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}
fn functionParamList(&self) -> Option<Rc<FunctionParamListContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}
fn whereClause(&self) -> Option<Rc<WhereClauseContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}
fn blockPredicate(&self) -> Option<Rc<BlockPredicateContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}
/// Retrieves first TerminalNode corresponding to token COMMA
/// Returns `None` if there is no child corresponding to token COMMA
fn COMMA(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(COMMA, 0)
}

}

impl<'input> PredDeclContextAttrs<'input> for PredDeclContext<'input>{}

impl<'input, I, H> LibSLParser<'input, I, H>
where
    I: TokenStream<'input, TF = LocalTokenFactory<'input> > + TidAble<'input>,
    H: ErrorStrategy<'input,BaseParserType<'input,I>>
{
	pub fn predDecl(&mut self,)
	-> Result<Rc<PredDeclContextAll<'input>>,ANTLRError> {
		let mut recog = self;
		let _parentctx = recog.ctx.take();
		let mut _localctx = PredDeclContextExt::new(_parentctx.clone(), recog.base.get_state());
        recog.base.enter_rule(_localctx.clone(), 66, RULE_predDecl);
        let mut _localctx: Rc<PredDeclContextAll> = _localctx;
		let mut _la: isize = -1;
		let result: Result<(), ANTLRError> = (|| {

			//recog.base.enter_outer_alt(_localctx.clone(), 1);
			recog.base.enter_outer_alt(None, 1);
			{
			recog.base.set_state(601);
			recog.err_handler.sync(&mut recog.base)?;
			_la = recog.base.input.la(1);
			while _la==AT {
				{
				{
				/*InvokeRule annotation*/
				recog.base.set_state(598);
				let tmp = recog.annotation()?;
				 cast_mut::<_,PredDeclContext >(&mut _localctx).annotation = Some(tmp.clone());
				  

				let temp =  cast_mut::<_,PredDeclContext >(&mut _localctx).annotation.clone().unwrap()
				 ;
				 cast_mut::<_,PredDeclContext >(&mut _localctx).annotations.push(temp);
				  
				}
				}
				recog.base.set_state(603);
				recog.err_handler.sync(&mut recog.base)?;
				_la = recog.base.input.la(1);
			}
			recog.base.set_state(604);
			recog.base.match_token(PRED,&mut recog.err_handler)?;

			/*InvokeRule ident*/
			recog.base.set_state(605);
			let tmp = recog.ident()?;
			 cast_mut::<_,PredDeclContext >(&mut _localctx).name = Some(tmp.clone());
			  

			recog.base.set_state(607);
			recog.err_handler.sync(&mut recog.base)?;
			_la = recog.base.input.la(1);
			if _la==L_ANGLE {
				{
				/*InvokeRule generics*/
				recog.base.set_state(606);
				let tmp = recog.generics()?;
				 cast_mut::<_,PredDeclContext >(&mut _localctx).typeParams = Some(tmp.clone());
				  

				}
			}

			recog.base.set_state(609);
			recog.base.match_token(L_PAREN,&mut recog.err_handler)?;

			recog.base.set_state(614);
			recog.err_handler.sync(&mut recog.base)?;
			_la = recog.base.input.la(1);
			if ((((_la - 86)) & !0x3f) == 0 && ((1usize << (_la - 86)) & 647) != 0) {
				{
				/*InvokeRule functionParamList*/
				recog.base.set_state(610);
				let tmp = recog.functionParamList()?;
				 cast_mut::<_,PredDeclContext >(&mut _localctx).params = Some(tmp.clone());
				  

				recog.base.set_state(612);
				recog.err_handler.sync(&mut recog.base)?;
				_la = recog.base.input.la(1);
				if _la==COMMA {
					{
					recog.base.set_state(611);
					recog.base.match_token(COMMA,&mut recog.err_handler)?;

					}
				}

				}
			}

			recog.base.set_state(616);
			recog.base.match_token(R_PAREN,&mut recog.err_handler)?;

			recog.base.set_state(618);
			recog.err_handler.sync(&mut recog.base)?;
			_la = recog.base.input.la(1);
			if _la==WHERE {
				{
				/*InvokeRule whereClause*/
				recog.base.set_state(617);
				let tmp = recog.whereClause()?;
				 cast_mut::<_,PredDeclContext >(&mut _localctx).typeConstraints = Some(tmp.clone());
				  

				}
			}

			recog.base.set_state(621);
			recog.err_handler.sync(&mut recog.base)?;
			_la = recog.base.input.la(1);
			if _la==L_BRACE {
				{
				/*InvokeRule blockPredicate*/
				recog.base.set_state(620);
				let tmp = recog.blockPredicate()?;
				 cast_mut::<_,PredDeclContext >(&mut _localctx).def = Some(tmp.clone());
				  

				}
			}

			}
			Ok(())
		})();
		match result {
		Ok(_)=>{},
        Err(e @ ANTLRError::FallThrough(_)) => return Err(e),
		Err(ref re) => {
				//_localctx.exception = re;
				recog.err_handler.report_error(&mut recog.base, re);
				recog.err_handler.recover(&mut recog.base, re)?;
			}
		}
		recog.base.exit_rule();

		Ok(_localctx)
	}
}
//------------------- variableDecl ----------------
pub type VariableDeclContextAll<'input> = VariableDeclContext<'input>;


pub type VariableDeclContext<'input> = BaseParserRuleContext<'input,VariableDeclContextExt<'input>>;

#[derive(Clone)]
pub struct VariableDeclContextExt<'input>{
	pub annotation: Option<Rc<AnnotationContextAll<'input>>>,
	pub annotations:Vec<Rc<AnnotationContextAll<'input>>>,
	pub kind: Option<Rc<VariableKindContextAll<'input>>>,
	pub name: Option<Rc<IdentContextAll<'input>>>,
	pub r#type: Option<Rc<TypeExprContextAll<'input>>>,
	pub init: Option<Rc<ExprContextAll<'input>>>,
ph:PhantomData<&'input str>
}

impl<'input> LibSLParserContext<'input> for VariableDeclContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for VariableDeclContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_variableDecl(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_variableDecl(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for VariableDeclContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_variableDecl }
	//fn type_rule_index() -> usize where Self: Sized { RULE_variableDecl }
}
antlr_rust::tid!{VariableDeclContextExt<'a>}

impl<'input> VariableDeclContextExt<'input>{
	fn new(parent: Option<Rc<dyn LibSLParserContext<'input> + 'input > >, invoking_state: isize) -> Rc<VariableDeclContextAll<'input>> {
		Rc::new(
			BaseParserRuleContext::new_parser_ctx(parent, invoking_state,VariableDeclContextExt{
				annotation: None, kind: None, name: None, r#type: None, init: None, 
				annotations: Vec::new(), 
				ph:PhantomData
			}),
		)
	}
}

pub trait VariableDeclContextAttrs<'input>: LibSLParserContext<'input> + BorrowMut<VariableDeclContextExt<'input>>{

/// Retrieves first TerminalNode corresponding to token SEMICOLON
/// Returns `None` if there is no child corresponding to token SEMICOLON
fn SEMICOLON(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(SEMICOLON, 0)
}
fn variableKind(&self) -> Option<Rc<VariableKindContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}
fn ident(&self) -> Option<Rc<IdentContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}
/// Retrieves first TerminalNode corresponding to token COLON
/// Returns `None` if there is no child corresponding to token COLON
fn COLON(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(COLON, 0)
}
/// Retrieves first TerminalNode corresponding to token EQ
/// Returns `None` if there is no child corresponding to token EQ
fn EQ(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(EQ, 0)
}
fn annotation_all(&self) ->  Vec<Rc<AnnotationContextAll<'input>>> where Self:Sized{
	self.children_of_type()
}
fn annotation(&self, i: usize) -> Option<Rc<AnnotationContextAll<'input>>> where Self:Sized{
	self.child_of_type(i)
}
fn typeExpr(&self) -> Option<Rc<TypeExprContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}
fn expr(&self) -> Option<Rc<ExprContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}

}

impl<'input> VariableDeclContextAttrs<'input> for VariableDeclContext<'input>{}

impl<'input, I, H> LibSLParser<'input, I, H>
where
    I: TokenStream<'input, TF = LocalTokenFactory<'input> > + TidAble<'input>,
    H: ErrorStrategy<'input,BaseParserType<'input,I>>
{
	pub fn variableDecl(&mut self,)
	-> Result<Rc<VariableDeclContextAll<'input>>,ANTLRError> {
		let mut recog = self;
		let _parentctx = recog.ctx.take();
		let mut _localctx = VariableDeclContextExt::new(_parentctx.clone(), recog.base.get_state());
        recog.base.enter_rule(_localctx.clone(), 68, RULE_variableDecl);
        let mut _localctx: Rc<VariableDeclContextAll> = _localctx;
		let mut _la: isize = -1;
		let result: Result<(), ANTLRError> = (|| {

			//recog.base.enter_outer_alt(_localctx.clone(), 1);
			recog.base.enter_outer_alt(None, 1);
			{
			recog.base.set_state(626);
			recog.err_handler.sync(&mut recog.base)?;
			_la = recog.base.input.la(1);
			while _la==AT {
				{
				{
				/*InvokeRule annotation*/
				recog.base.set_state(623);
				let tmp = recog.annotation()?;
				 cast_mut::<_,VariableDeclContext >(&mut _localctx).annotation = Some(tmp.clone());
				  

				let temp =  cast_mut::<_,VariableDeclContext >(&mut _localctx).annotation.clone().unwrap()
				 ;
				 cast_mut::<_,VariableDeclContext >(&mut _localctx).annotations.push(temp);
				  
				}
				}
				recog.base.set_state(628);
				recog.err_handler.sync(&mut recog.base)?;
				_la = recog.base.input.la(1);
			}
			/*InvokeRule variableKind*/
			recog.base.set_state(629);
			let tmp = recog.variableKind()?;
			 cast_mut::<_,VariableDeclContext >(&mut _localctx).kind = Some(tmp.clone());
			  

			/*InvokeRule ident*/
			recog.base.set_state(630);
			let tmp = recog.ident()?;
			 cast_mut::<_,VariableDeclContext >(&mut _localctx).name = Some(tmp.clone());
			  

			recog.base.set_state(633);
			recog.err_handler.sync(&mut recog.base)?;
			_la = recog.base.input.la(1);
			if _la==COLON {
				{
				recog.base.set_state(631);
				recog.base.match_token(COLON,&mut recog.err_handler)?;

				/*InvokeRule typeExpr*/
				recog.base.set_state(632);
				let tmp = recog.typeExpr_rec(0)?;
				 cast_mut::<_,VariableDeclContext >(&mut _localctx).r#type = Some(tmp.clone());
				  

				}
			}

			recog.base.set_state(637);
			recog.err_handler.sync(&mut recog.base)?;
			_la = recog.base.input.la(1);
			if _la==EQ {
				{
				recog.base.set_state(635);
				recog.base.match_token(EQ,&mut recog.err_handler)?;

				/*InvokeRule expr*/
				recog.base.set_state(636);
				let tmp = recog.expr_rec(0)?;
				 cast_mut::<_,VariableDeclContext >(&mut _localctx).init = Some(tmp.clone());
				  

				}
			}

			recog.base.set_state(639);
			recog.base.match_token(SEMICOLON,&mut recog.err_handler)?;

			}
			Ok(())
		})();
		match result {
		Ok(_)=>{},
        Err(e @ ANTLRError::FallThrough(_)) => return Err(e),
		Err(ref re) => {
				//_localctx.exception = re;
				recog.err_handler.report_error(&mut recog.base, re);
				recog.err_handler.recover(&mut recog.base, re)?;
			}
		}
		recog.base.exit_rule();

		Ok(_localctx)
	}
}
//------------------- variableKind ----------------
#[derive(Debug)]
pub enum VariableKindContextAll<'input>{
	VariableKindVarContext(VariableKindVarContext<'input>),
	VariableKindValContext(VariableKindValContext<'input>),
Error(VariableKindContext<'input>)
}
antlr_rust::tid!{VariableKindContextAll<'a>}

impl<'input> antlr_rust::parser_rule_context::DerefSeal for VariableKindContextAll<'input>{}

impl<'input> LibSLParserContext<'input> for VariableKindContextAll<'input>{}

impl<'input> Deref for VariableKindContextAll<'input>{
	type Target = dyn VariableKindContextAttrs<'input> + 'input;
	fn deref(&self) -> &Self::Target{
		use VariableKindContextAll::*;
		match self{
			VariableKindVarContext(inner) => inner,
			VariableKindValContext(inner) => inner,
Error(inner) => inner
		}
	}
}
impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for VariableKindContextAll<'input>{
    fn enter(&self, listener: &mut (dyn LibSLParserListener<'input> + 'a)) { self.deref().enter(listener) }
    fn exit(&self, listener: &mut (dyn LibSLParserListener<'input> + 'a)) { self.deref().exit(listener) }
}



pub type VariableKindContext<'input> = BaseParserRuleContext<'input,VariableKindContextExt<'input>>;

#[derive(Clone)]
pub struct VariableKindContextExt<'input>{
ph:PhantomData<&'input str>
}

impl<'input> LibSLParserContext<'input> for VariableKindContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for VariableKindContext<'input>{
}

impl<'input> CustomRuleContext<'input> for VariableKindContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_variableKind }
	//fn type_rule_index() -> usize where Self: Sized { RULE_variableKind }
}
antlr_rust::tid!{VariableKindContextExt<'a>}

impl<'input> VariableKindContextExt<'input>{
	fn new(parent: Option<Rc<dyn LibSLParserContext<'input> + 'input > >, invoking_state: isize) -> Rc<VariableKindContextAll<'input>> {
		Rc::new(
		VariableKindContextAll::Error(
			BaseParserRuleContext::new_parser_ctx(parent, invoking_state,VariableKindContextExt{
				ph:PhantomData
			}),
		)
		)
	}
}

pub trait VariableKindContextAttrs<'input>: LibSLParserContext<'input> + BorrowMut<VariableKindContextExt<'input>>{


}

impl<'input> VariableKindContextAttrs<'input> for VariableKindContext<'input>{}

pub type VariableKindVarContext<'input> = BaseParserRuleContext<'input,VariableKindVarContextExt<'input>>;

pub trait VariableKindVarContextAttrs<'input>: LibSLParserContext<'input>{
	/// Retrieves first TerminalNode corresponding to token VAR
	/// Returns `None` if there is no child corresponding to token VAR
	fn VAR(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(VAR, 0)
	}
}

impl<'input> VariableKindVarContextAttrs<'input> for VariableKindVarContext<'input>{}

pub struct VariableKindVarContextExt<'input>{
	__base:VariableKindContextExt<'input>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{VariableKindVarContextExt<'a>}

impl<'input> LibSLParserContext<'input> for VariableKindVarContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for VariableKindVarContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_VariableKindVar(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_VariableKindVar(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for VariableKindVarContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_variableKind }
	//fn type_rule_index() -> usize where Self: Sized { RULE_variableKind }
}

impl<'input> Borrow<VariableKindContextExt<'input>> for VariableKindVarContext<'input>{
	fn borrow(&self) -> &VariableKindContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<VariableKindContextExt<'input>> for VariableKindVarContext<'input>{
	fn borrow_mut(&mut self) -> &mut VariableKindContextExt<'input> { &mut self.__base }
}

impl<'input> VariableKindContextAttrs<'input> for VariableKindVarContext<'input> {}

impl<'input> VariableKindVarContextExt<'input>{
	fn new(ctx: &dyn VariableKindContextAttrs<'input>) -> Rc<VariableKindContextAll<'input>>  {
		Rc::new(
			VariableKindContextAll::VariableKindVarContext(
				BaseParserRuleContext::copy_from(ctx,VariableKindVarContextExt{
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type VariableKindValContext<'input> = BaseParserRuleContext<'input,VariableKindValContextExt<'input>>;

pub trait VariableKindValContextAttrs<'input>: LibSLParserContext<'input>{
	/// Retrieves first TerminalNode corresponding to token VAL
	/// Returns `None` if there is no child corresponding to token VAL
	fn VAL(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(VAL, 0)
	}
}

impl<'input> VariableKindValContextAttrs<'input> for VariableKindValContext<'input>{}

pub struct VariableKindValContextExt<'input>{
	__base:VariableKindContextExt<'input>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{VariableKindValContextExt<'a>}

impl<'input> LibSLParserContext<'input> for VariableKindValContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for VariableKindValContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_VariableKindVal(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_VariableKindVal(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for VariableKindValContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_variableKind }
	//fn type_rule_index() -> usize where Self: Sized { RULE_variableKind }
}

impl<'input> Borrow<VariableKindContextExt<'input>> for VariableKindValContext<'input>{
	fn borrow(&self) -> &VariableKindContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<VariableKindContextExt<'input>> for VariableKindValContext<'input>{
	fn borrow_mut(&mut self) -> &mut VariableKindContextExt<'input> { &mut self.__base }
}

impl<'input> VariableKindContextAttrs<'input> for VariableKindValContext<'input> {}

impl<'input> VariableKindValContextExt<'input>{
	fn new(ctx: &dyn VariableKindContextAttrs<'input>) -> Rc<VariableKindContextAll<'input>>  {
		Rc::new(
			VariableKindContextAll::VariableKindValContext(
				BaseParserRuleContext::copy_from(ctx,VariableKindValContextExt{
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

impl<'input, I, H> LibSLParser<'input, I, H>
where
    I: TokenStream<'input, TF = LocalTokenFactory<'input> > + TidAble<'input>,
    H: ErrorStrategy<'input,BaseParserType<'input,I>>
{
	pub fn variableKind(&mut self,)
	-> Result<Rc<VariableKindContextAll<'input>>,ANTLRError> {
		let mut recog = self;
		let _parentctx = recog.ctx.take();
		let mut _localctx = VariableKindContextExt::new(_parentctx.clone(), recog.base.get_state());
        recog.base.enter_rule(_localctx.clone(), 70, RULE_variableKind);
        let mut _localctx: Rc<VariableKindContextAll> = _localctx;
		let result: Result<(), ANTLRError> = (|| {

			recog.base.set_state(643);
			recog.err_handler.sync(&mut recog.base)?;
			match recog.base.input.la(1) {
			 VAR 
				=> {
					let tmp = VariableKindVarContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 1);
					_localctx = tmp;
					{
					recog.base.set_state(641);
					recog.base.match_token(VAR,&mut recog.err_handler)?;

					}
				}

			 VAL 
				=> {
					let tmp = VariableKindValContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 2);
					_localctx = tmp;
					{
					recog.base.set_state(642);
					recog.base.match_token(VAL,&mut recog.err_handler)?;

					}
				}

				_ => Err(ANTLRError::NoAltError(NoViableAltError::new(&mut recog.base)))?
			}
			Ok(())
		})();
		match result {
		Ok(_)=>{},
        Err(e @ ANTLRError::FallThrough(_)) => return Err(e),
		Err(ref re) => {
				//_localctx.exception = re;
				recog.err_handler.report_error(&mut recog.base, re);
				recog.err_handler.recover(&mut recog.base, re)?;
			}
		}
		recog.base.exit_rule();

		Ok(_localctx)
	}
}
//------------------- stateDecl ----------------
pub type StateDeclContextAll<'input> = StateDeclContext<'input>;


pub type StateDeclContext<'input> = BaseParserRuleContext<'input,StateDeclContextExt<'input>>;

#[derive(Clone)]
pub struct StateDeclContextExt<'input>{
	pub kind: Option<Rc<StateKindContextAll<'input>>>,
	pub names: Option<Rc<IdentListContextAll<'input>>>,
ph:PhantomData<&'input str>
}

impl<'input> LibSLParserContext<'input> for StateDeclContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for StateDeclContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_stateDecl(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_stateDecl(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for StateDeclContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_stateDecl }
	//fn type_rule_index() -> usize where Self: Sized { RULE_stateDecl }
}
antlr_rust::tid!{StateDeclContextExt<'a>}

impl<'input> StateDeclContextExt<'input>{
	fn new(parent: Option<Rc<dyn LibSLParserContext<'input> + 'input > >, invoking_state: isize) -> Rc<StateDeclContextAll<'input>> {
		Rc::new(
			BaseParserRuleContext::new_parser_ctx(parent, invoking_state,StateDeclContextExt{
				kind: None, names: None, 
				ph:PhantomData
			}),
		)
	}
}

pub trait StateDeclContextAttrs<'input>: LibSLParserContext<'input> + BorrowMut<StateDeclContextExt<'input>>{

/// Retrieves first TerminalNode corresponding to token SEMICOLON
/// Returns `None` if there is no child corresponding to token SEMICOLON
fn SEMICOLON(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(SEMICOLON, 0)
}
fn stateKind(&self) -> Option<Rc<StateKindContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}
fn identList(&self) -> Option<Rc<IdentListContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}

}

impl<'input> StateDeclContextAttrs<'input> for StateDeclContext<'input>{}

impl<'input, I, H> LibSLParser<'input, I, H>
where
    I: TokenStream<'input, TF = LocalTokenFactory<'input> > + TidAble<'input>,
    H: ErrorStrategy<'input,BaseParserType<'input,I>>
{
	pub fn stateDecl(&mut self,)
	-> Result<Rc<StateDeclContextAll<'input>>,ANTLRError> {
		let mut recog = self;
		let _parentctx = recog.ctx.take();
		let mut _localctx = StateDeclContextExt::new(_parentctx.clone(), recog.base.get_state());
        recog.base.enter_rule(_localctx.clone(), 72, RULE_stateDecl);
        let mut _localctx: Rc<StateDeclContextAll> = _localctx;
		let result: Result<(), ANTLRError> = (|| {

			//recog.base.enter_outer_alt(_localctx.clone(), 1);
			recog.base.enter_outer_alt(None, 1);
			{
			/*InvokeRule stateKind*/
			recog.base.set_state(645);
			let tmp = recog.stateKind()?;
			 cast_mut::<_,StateDeclContext >(&mut _localctx).kind = Some(tmp.clone());
			  

			/*InvokeRule identList*/
			recog.base.set_state(646);
			let tmp = recog.identList()?;
			 cast_mut::<_,StateDeclContext >(&mut _localctx).names = Some(tmp.clone());
			  

			recog.base.set_state(647);
			recog.base.match_token(SEMICOLON,&mut recog.err_handler)?;

			}
			Ok(())
		})();
		match result {
		Ok(_)=>{},
        Err(e @ ANTLRError::FallThrough(_)) => return Err(e),
		Err(ref re) => {
				//_localctx.exception = re;
				recog.err_handler.report_error(&mut recog.base, re);
				recog.err_handler.recover(&mut recog.base, re)?;
			}
		}
		recog.base.exit_rule();

		Ok(_localctx)
	}
}
//------------------- stateKind ----------------
#[derive(Debug)]
pub enum StateKindContextAll<'input>{
	StateKindInitialContext(StateKindInitialContext<'input>),
	StateKindFinalContext(StateKindFinalContext<'input>),
	StateKindRegularContext(StateKindRegularContext<'input>),
Error(StateKindContext<'input>)
}
antlr_rust::tid!{StateKindContextAll<'a>}

impl<'input> antlr_rust::parser_rule_context::DerefSeal for StateKindContextAll<'input>{}

impl<'input> LibSLParserContext<'input> for StateKindContextAll<'input>{}

impl<'input> Deref for StateKindContextAll<'input>{
	type Target = dyn StateKindContextAttrs<'input> + 'input;
	fn deref(&self) -> &Self::Target{
		use StateKindContextAll::*;
		match self{
			StateKindInitialContext(inner) => inner,
			StateKindFinalContext(inner) => inner,
			StateKindRegularContext(inner) => inner,
Error(inner) => inner
		}
	}
}
impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for StateKindContextAll<'input>{
    fn enter(&self, listener: &mut (dyn LibSLParserListener<'input> + 'a)) { self.deref().enter(listener) }
    fn exit(&self, listener: &mut (dyn LibSLParserListener<'input> + 'a)) { self.deref().exit(listener) }
}



pub type StateKindContext<'input> = BaseParserRuleContext<'input,StateKindContextExt<'input>>;

#[derive(Clone)]
pub struct StateKindContextExt<'input>{
ph:PhantomData<&'input str>
}

impl<'input> LibSLParserContext<'input> for StateKindContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for StateKindContext<'input>{
}

impl<'input> CustomRuleContext<'input> for StateKindContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_stateKind }
	//fn type_rule_index() -> usize where Self: Sized { RULE_stateKind }
}
antlr_rust::tid!{StateKindContextExt<'a>}

impl<'input> StateKindContextExt<'input>{
	fn new(parent: Option<Rc<dyn LibSLParserContext<'input> + 'input > >, invoking_state: isize) -> Rc<StateKindContextAll<'input>> {
		Rc::new(
		StateKindContextAll::Error(
			BaseParserRuleContext::new_parser_ctx(parent, invoking_state,StateKindContextExt{
				ph:PhantomData
			}),
		)
		)
	}
}

pub trait StateKindContextAttrs<'input>: LibSLParserContext<'input> + BorrowMut<StateKindContextExt<'input>>{


}

impl<'input> StateKindContextAttrs<'input> for StateKindContext<'input>{}

pub type StateKindInitialContext<'input> = BaseParserRuleContext<'input,StateKindInitialContextExt<'input>>;

pub trait StateKindInitialContextAttrs<'input>: LibSLParserContext<'input>{
	/// Retrieves first TerminalNode corresponding to token INITSTATE
	/// Returns `None` if there is no child corresponding to token INITSTATE
	fn INITSTATE(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(INITSTATE, 0)
	}
}

impl<'input> StateKindInitialContextAttrs<'input> for StateKindInitialContext<'input>{}

pub struct StateKindInitialContextExt<'input>{
	__base:StateKindContextExt<'input>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{StateKindInitialContextExt<'a>}

impl<'input> LibSLParserContext<'input> for StateKindInitialContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for StateKindInitialContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_StateKindInitial(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_StateKindInitial(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for StateKindInitialContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_stateKind }
	//fn type_rule_index() -> usize where Self: Sized { RULE_stateKind }
}

impl<'input> Borrow<StateKindContextExt<'input>> for StateKindInitialContext<'input>{
	fn borrow(&self) -> &StateKindContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<StateKindContextExt<'input>> for StateKindInitialContext<'input>{
	fn borrow_mut(&mut self) -> &mut StateKindContextExt<'input> { &mut self.__base }
}

impl<'input> StateKindContextAttrs<'input> for StateKindInitialContext<'input> {}

impl<'input> StateKindInitialContextExt<'input>{
	fn new(ctx: &dyn StateKindContextAttrs<'input>) -> Rc<StateKindContextAll<'input>>  {
		Rc::new(
			StateKindContextAll::StateKindInitialContext(
				BaseParserRuleContext::copy_from(ctx,StateKindInitialContextExt{
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type StateKindFinalContext<'input> = BaseParserRuleContext<'input,StateKindFinalContextExt<'input>>;

pub trait StateKindFinalContextAttrs<'input>: LibSLParserContext<'input>{
	/// Retrieves first TerminalNode corresponding to token FINISHSTATE
	/// Returns `None` if there is no child corresponding to token FINISHSTATE
	fn FINISHSTATE(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(FINISHSTATE, 0)
	}
}

impl<'input> StateKindFinalContextAttrs<'input> for StateKindFinalContext<'input>{}

pub struct StateKindFinalContextExt<'input>{
	__base:StateKindContextExt<'input>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{StateKindFinalContextExt<'a>}

impl<'input> LibSLParserContext<'input> for StateKindFinalContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for StateKindFinalContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_StateKindFinal(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_StateKindFinal(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for StateKindFinalContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_stateKind }
	//fn type_rule_index() -> usize where Self: Sized { RULE_stateKind }
}

impl<'input> Borrow<StateKindContextExt<'input>> for StateKindFinalContext<'input>{
	fn borrow(&self) -> &StateKindContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<StateKindContextExt<'input>> for StateKindFinalContext<'input>{
	fn borrow_mut(&mut self) -> &mut StateKindContextExt<'input> { &mut self.__base }
}

impl<'input> StateKindContextAttrs<'input> for StateKindFinalContext<'input> {}

impl<'input> StateKindFinalContextExt<'input>{
	fn new(ctx: &dyn StateKindContextAttrs<'input>) -> Rc<StateKindContextAll<'input>>  {
		Rc::new(
			StateKindContextAll::StateKindFinalContext(
				BaseParserRuleContext::copy_from(ctx,StateKindFinalContextExt{
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type StateKindRegularContext<'input> = BaseParserRuleContext<'input,StateKindRegularContextExt<'input>>;

pub trait StateKindRegularContextAttrs<'input>: LibSLParserContext<'input>{
	/// Retrieves first TerminalNode corresponding to token STATE
	/// Returns `None` if there is no child corresponding to token STATE
	fn STATE(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(STATE, 0)
	}
}

impl<'input> StateKindRegularContextAttrs<'input> for StateKindRegularContext<'input>{}

pub struct StateKindRegularContextExt<'input>{
	__base:StateKindContextExt<'input>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{StateKindRegularContextExt<'a>}

impl<'input> LibSLParserContext<'input> for StateKindRegularContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for StateKindRegularContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_StateKindRegular(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_StateKindRegular(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for StateKindRegularContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_stateKind }
	//fn type_rule_index() -> usize where Self: Sized { RULE_stateKind }
}

impl<'input> Borrow<StateKindContextExt<'input>> for StateKindRegularContext<'input>{
	fn borrow(&self) -> &StateKindContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<StateKindContextExt<'input>> for StateKindRegularContext<'input>{
	fn borrow_mut(&mut self) -> &mut StateKindContextExt<'input> { &mut self.__base }
}

impl<'input> StateKindContextAttrs<'input> for StateKindRegularContext<'input> {}

impl<'input> StateKindRegularContextExt<'input>{
	fn new(ctx: &dyn StateKindContextAttrs<'input>) -> Rc<StateKindContextAll<'input>>  {
		Rc::new(
			StateKindContextAll::StateKindRegularContext(
				BaseParserRuleContext::copy_from(ctx,StateKindRegularContextExt{
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

impl<'input, I, H> LibSLParser<'input, I, H>
where
    I: TokenStream<'input, TF = LocalTokenFactory<'input> > + TidAble<'input>,
    H: ErrorStrategy<'input,BaseParserType<'input,I>>
{
	pub fn stateKind(&mut self,)
	-> Result<Rc<StateKindContextAll<'input>>,ANTLRError> {
		let mut recog = self;
		let _parentctx = recog.ctx.take();
		let mut _localctx = StateKindContextExt::new(_parentctx.clone(), recog.base.get_state());
        recog.base.enter_rule(_localctx.clone(), 74, RULE_stateKind);
        let mut _localctx: Rc<StateKindContextAll> = _localctx;
		let result: Result<(), ANTLRError> = (|| {

			recog.base.set_state(652);
			recog.err_handler.sync(&mut recog.base)?;
			match recog.base.input.la(1) {
			 INITSTATE 
				=> {
					let tmp = StateKindInitialContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 1);
					_localctx = tmp;
					{
					recog.base.set_state(649);
					recog.base.match_token(INITSTATE,&mut recog.err_handler)?;

					}
				}

			 STATE 
				=> {
					let tmp = StateKindRegularContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 2);
					_localctx = tmp;
					{
					recog.base.set_state(650);
					recog.base.match_token(STATE,&mut recog.err_handler)?;

					}
				}

			 FINISHSTATE 
				=> {
					let tmp = StateKindFinalContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 3);
					_localctx = tmp;
					{
					recog.base.set_state(651);
					recog.base.match_token(FINISHSTATE,&mut recog.err_handler)?;

					}
				}

				_ => Err(ANTLRError::NoAltError(NoViableAltError::new(&mut recog.base)))?
			}
			Ok(())
		})();
		match result {
		Ok(_)=>{},
        Err(e @ ANTLRError::FallThrough(_)) => return Err(e),
		Err(ref re) => {
				//_localctx.exception = re;
				recog.err_handler.report_error(&mut recog.base, re);
				recog.err_handler.recover(&mut recog.base, re)?;
			}
		}
		recog.base.exit_rule();

		Ok(_localctx)
	}
}
//------------------- identList ----------------
pub type IdentListContextAll<'input> = IdentListContext<'input>;


pub type IdentListContext<'input> = BaseParserRuleContext<'input,IdentListContextExt<'input>>;

#[derive(Clone)]
pub struct IdentListContextExt<'input>{
	pub ident: Option<Rc<IdentContextAll<'input>>>,
	pub names:Vec<Rc<IdentContextAll<'input>>>,
ph:PhantomData<&'input str>
}

impl<'input> LibSLParserContext<'input> for IdentListContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for IdentListContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_identList(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_identList(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for IdentListContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_identList }
	//fn type_rule_index() -> usize where Self: Sized { RULE_identList }
}
antlr_rust::tid!{IdentListContextExt<'a>}

impl<'input> IdentListContextExt<'input>{
	fn new(parent: Option<Rc<dyn LibSLParserContext<'input> + 'input > >, invoking_state: isize) -> Rc<IdentListContextAll<'input>> {
		Rc::new(
			BaseParserRuleContext::new_parser_ctx(parent, invoking_state,IdentListContextExt{
				ident: None, 
				names: Vec::new(), 
				ph:PhantomData
			}),
		)
	}
}

pub trait IdentListContextAttrs<'input>: LibSLParserContext<'input> + BorrowMut<IdentListContextExt<'input>>{

fn ident_all(&self) ->  Vec<Rc<IdentContextAll<'input>>> where Self:Sized{
	self.children_of_type()
}
fn ident(&self, i: usize) -> Option<Rc<IdentContextAll<'input>>> where Self:Sized{
	self.child_of_type(i)
}
/// Retrieves all `TerminalNode`s corresponding to token COMMA in current rule
fn COMMA_all(&self) -> Vec<Rc<TerminalNode<'input,LibSLParserContextType>>>  where Self:Sized{
	self.get_tokens(COMMA)
}
/// Retrieves 'i's TerminalNode corresponding to token COMMA, starting from 0.
/// Returns `None` if number of children corresponding to token COMMA is less or equal than `i`.
fn COMMA(&self, i: usize) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(COMMA, i)
}

}

impl<'input> IdentListContextAttrs<'input> for IdentListContext<'input>{}

impl<'input, I, H> LibSLParser<'input, I, H>
where
    I: TokenStream<'input, TF = LocalTokenFactory<'input> > + TidAble<'input>,
    H: ErrorStrategy<'input,BaseParserType<'input,I>>
{
	pub fn identList(&mut self,)
	-> Result<Rc<IdentListContextAll<'input>>,ANTLRError> {
		let mut recog = self;
		let _parentctx = recog.ctx.take();
		let mut _localctx = IdentListContextExt::new(_parentctx.clone(), recog.base.get_state());
        recog.base.enter_rule(_localctx.clone(), 76, RULE_identList);
        let mut _localctx: Rc<IdentListContextAll> = _localctx;
		let result: Result<(), ANTLRError> = (|| {

			let mut _alt: isize;
			//recog.base.enter_outer_alt(_localctx.clone(), 1);
			recog.base.enter_outer_alt(None, 1);
			{
			/*InvokeRule ident*/
			recog.base.set_state(654);
			let tmp = recog.ident()?;
			 cast_mut::<_,IdentListContext >(&mut _localctx).ident = Some(tmp.clone());
			  

			let temp =  cast_mut::<_,IdentListContext >(&mut _localctx).ident.clone().unwrap()
			 ;
			 cast_mut::<_,IdentListContext >(&mut _localctx).names.push(temp);
			  
			recog.base.set_state(659);
			recog.err_handler.sync(&mut recog.base)?;
			_alt = recog.interpreter.adaptive_predict(72,&mut recog.base)?;
			while { _alt!=2 && _alt!=INVALID_ALT } {
				if _alt==1 {
					{
					{
					recog.base.set_state(655);
					recog.base.match_token(COMMA,&mut recog.err_handler)?;

					/*InvokeRule ident*/
					recog.base.set_state(656);
					let tmp = recog.ident()?;
					 cast_mut::<_,IdentListContext >(&mut _localctx).ident = Some(tmp.clone());
					  

					let temp =  cast_mut::<_,IdentListContext >(&mut _localctx).ident.clone().unwrap()
					 ;
					 cast_mut::<_,IdentListContext >(&mut _localctx).names.push(temp);
					  
					}
					} 
				}
				recog.base.set_state(661);
				recog.err_handler.sync(&mut recog.base)?;
				_alt = recog.interpreter.adaptive_predict(72,&mut recog.base)?;
			}
			}
			Ok(())
		})();
		match result {
		Ok(_)=>{},
        Err(e @ ANTLRError::FallThrough(_)) => return Err(e),
		Err(ref re) => {
				//_localctx.exception = re;
				recog.err_handler.report_error(&mut recog.base, re);
				recog.err_handler.recover(&mut recog.base, re)?;
			}
		}
		recog.base.exit_rule();

		Ok(_localctx)
	}
}
//------------------- shiftDecl ----------------
pub type ShiftDeclContextAll<'input> = ShiftDeclContext<'input>;


pub type ShiftDeclContext<'input> = BaseParserRuleContext<'input,ShiftDeclContextExt<'input>>;

#[derive(Clone)]
pub struct ShiftDeclContextExt<'input>{
	pub from: Option<Rc<ShiftSourceStateContextAll<'input>>>,
	pub to: Option<Rc<IdentContextAll<'input>>>,
	pub by: Option<Rc<ShiftByContextAll<'input>>>,
ph:PhantomData<&'input str>
}

impl<'input> LibSLParserContext<'input> for ShiftDeclContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for ShiftDeclContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_shiftDecl(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_shiftDecl(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for ShiftDeclContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_shiftDecl }
	//fn type_rule_index() -> usize where Self: Sized { RULE_shiftDecl }
}
antlr_rust::tid!{ShiftDeclContextExt<'a>}

impl<'input> ShiftDeclContextExt<'input>{
	fn new(parent: Option<Rc<dyn LibSLParserContext<'input> + 'input > >, invoking_state: isize) -> Rc<ShiftDeclContextAll<'input>> {
		Rc::new(
			BaseParserRuleContext::new_parser_ctx(parent, invoking_state,ShiftDeclContextExt{
				from: None, to: None, by: None, 
				ph:PhantomData
			}),
		)
	}
}

pub trait ShiftDeclContextAttrs<'input>: LibSLParserContext<'input> + BorrowMut<ShiftDeclContextExt<'input>>{

/// Retrieves first TerminalNode corresponding to token SHIFT
/// Returns `None` if there is no child corresponding to token SHIFT
fn SHIFT(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(SHIFT, 0)
}
/// Retrieves first TerminalNode corresponding to token ARROW
/// Returns `None` if there is no child corresponding to token ARROW
fn ARROW(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(ARROW, 0)
}
/// Retrieves first TerminalNode corresponding to token BY
/// Returns `None` if there is no child corresponding to token BY
fn BY(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(BY, 0)
}
/// Retrieves first TerminalNode corresponding to token SEMICOLON
/// Returns `None` if there is no child corresponding to token SEMICOLON
fn SEMICOLON(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(SEMICOLON, 0)
}
fn shiftSourceState(&self) -> Option<Rc<ShiftSourceStateContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}
fn ident(&self) -> Option<Rc<IdentContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}
fn shiftBy(&self) -> Option<Rc<ShiftByContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}

}

impl<'input> ShiftDeclContextAttrs<'input> for ShiftDeclContext<'input>{}

impl<'input, I, H> LibSLParser<'input, I, H>
where
    I: TokenStream<'input, TF = LocalTokenFactory<'input> > + TidAble<'input>,
    H: ErrorStrategy<'input,BaseParserType<'input,I>>
{
	pub fn shiftDecl(&mut self,)
	-> Result<Rc<ShiftDeclContextAll<'input>>,ANTLRError> {
		let mut recog = self;
		let _parentctx = recog.ctx.take();
		let mut _localctx = ShiftDeclContextExt::new(_parentctx.clone(), recog.base.get_state());
        recog.base.enter_rule(_localctx.clone(), 78, RULE_shiftDecl);
        let mut _localctx: Rc<ShiftDeclContextAll> = _localctx;
		let result: Result<(), ANTLRError> = (|| {

			//recog.base.enter_outer_alt(_localctx.clone(), 1);
			recog.base.enter_outer_alt(None, 1);
			{
			recog.base.set_state(662);
			recog.base.match_token(SHIFT,&mut recog.err_handler)?;

			/*InvokeRule shiftSourceState*/
			recog.base.set_state(663);
			let tmp = recog.shiftSourceState()?;
			 cast_mut::<_,ShiftDeclContext >(&mut _localctx).from = Some(tmp.clone());
			  

			recog.base.set_state(664);
			recog.base.match_token(ARROW,&mut recog.err_handler)?;

			/*InvokeRule ident*/
			recog.base.set_state(665);
			let tmp = recog.ident()?;
			 cast_mut::<_,ShiftDeclContext >(&mut _localctx).to = Some(tmp.clone());
			  

			recog.base.set_state(666);
			recog.base.match_token(BY,&mut recog.err_handler)?;

			/*InvokeRule shiftBy*/
			recog.base.set_state(667);
			let tmp = recog.shiftBy()?;
			 cast_mut::<_,ShiftDeclContext >(&mut _localctx).by = Some(tmp.clone());
			  

			recog.base.set_state(668);
			recog.base.match_token(SEMICOLON,&mut recog.err_handler)?;

			}
			Ok(())
		})();
		match result {
		Ok(_)=>{},
        Err(e @ ANTLRError::FallThrough(_)) => return Err(e),
		Err(ref re) => {
				//_localctx.exception = re;
				recog.err_handler.report_error(&mut recog.base, re);
				recog.err_handler.recover(&mut recog.base, re)?;
			}
		}
		recog.base.exit_rule();

		Ok(_localctx)
	}
}
//------------------- shiftSourceState ----------------
#[derive(Debug)]
pub enum ShiftSourceStateContextAll<'input>{
	ShiftSourceStateShorthandContext(ShiftSourceStateShorthandContext<'input>),
	ShiftSourceStateListContext(ShiftSourceStateListContext<'input>),
Error(ShiftSourceStateContext<'input>)
}
antlr_rust::tid!{ShiftSourceStateContextAll<'a>}

impl<'input> antlr_rust::parser_rule_context::DerefSeal for ShiftSourceStateContextAll<'input>{}

impl<'input> LibSLParserContext<'input> for ShiftSourceStateContextAll<'input>{}

impl<'input> Deref for ShiftSourceStateContextAll<'input>{
	type Target = dyn ShiftSourceStateContextAttrs<'input> + 'input;
	fn deref(&self) -> &Self::Target{
		use ShiftSourceStateContextAll::*;
		match self{
			ShiftSourceStateShorthandContext(inner) => inner,
			ShiftSourceStateListContext(inner) => inner,
Error(inner) => inner
		}
	}
}
impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for ShiftSourceStateContextAll<'input>{
    fn enter(&self, listener: &mut (dyn LibSLParserListener<'input> + 'a)) { self.deref().enter(listener) }
    fn exit(&self, listener: &mut (dyn LibSLParserListener<'input> + 'a)) { self.deref().exit(listener) }
}



pub type ShiftSourceStateContext<'input> = BaseParserRuleContext<'input,ShiftSourceStateContextExt<'input>>;

#[derive(Clone)]
pub struct ShiftSourceStateContextExt<'input>{
ph:PhantomData<&'input str>
}

impl<'input> LibSLParserContext<'input> for ShiftSourceStateContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for ShiftSourceStateContext<'input>{
}

impl<'input> CustomRuleContext<'input> for ShiftSourceStateContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_shiftSourceState }
	//fn type_rule_index() -> usize where Self: Sized { RULE_shiftSourceState }
}
antlr_rust::tid!{ShiftSourceStateContextExt<'a>}

impl<'input> ShiftSourceStateContextExt<'input>{
	fn new(parent: Option<Rc<dyn LibSLParserContext<'input> + 'input > >, invoking_state: isize) -> Rc<ShiftSourceStateContextAll<'input>> {
		Rc::new(
		ShiftSourceStateContextAll::Error(
			BaseParserRuleContext::new_parser_ctx(parent, invoking_state,ShiftSourceStateContextExt{
				ph:PhantomData
			}),
		)
		)
	}
}

pub trait ShiftSourceStateContextAttrs<'input>: LibSLParserContext<'input> + BorrowMut<ShiftSourceStateContextExt<'input>>{


}

impl<'input> ShiftSourceStateContextAttrs<'input> for ShiftSourceStateContext<'input>{}

pub type ShiftSourceStateShorthandContext<'input> = BaseParserRuleContext<'input,ShiftSourceStateShorthandContextExt<'input>>;

pub trait ShiftSourceStateShorthandContextAttrs<'input>: LibSLParserContext<'input>{
	fn ident(&self) -> Option<Rc<IdentContextAll<'input>>> where Self:Sized{
		self.child_of_type(0)
	}
}

impl<'input> ShiftSourceStateShorthandContextAttrs<'input> for ShiftSourceStateShorthandContext<'input>{}

pub struct ShiftSourceStateShorthandContextExt<'input>{
	__base:ShiftSourceStateContextExt<'input>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{ShiftSourceStateShorthandContextExt<'a>}

impl<'input> LibSLParserContext<'input> for ShiftSourceStateShorthandContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for ShiftSourceStateShorthandContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_ShiftSourceStateShorthand(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_ShiftSourceStateShorthand(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for ShiftSourceStateShorthandContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_shiftSourceState }
	//fn type_rule_index() -> usize where Self: Sized { RULE_shiftSourceState }
}

impl<'input> Borrow<ShiftSourceStateContextExt<'input>> for ShiftSourceStateShorthandContext<'input>{
	fn borrow(&self) -> &ShiftSourceStateContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<ShiftSourceStateContextExt<'input>> for ShiftSourceStateShorthandContext<'input>{
	fn borrow_mut(&mut self) -> &mut ShiftSourceStateContextExt<'input> { &mut self.__base }
}

impl<'input> ShiftSourceStateContextAttrs<'input> for ShiftSourceStateShorthandContext<'input> {}

impl<'input> ShiftSourceStateShorthandContextExt<'input>{
	fn new(ctx: &dyn ShiftSourceStateContextAttrs<'input>) -> Rc<ShiftSourceStateContextAll<'input>>  {
		Rc::new(
			ShiftSourceStateContextAll::ShiftSourceStateShorthandContext(
				BaseParserRuleContext::copy_from(ctx,ShiftSourceStateShorthandContextExt{
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type ShiftSourceStateListContext<'input> = BaseParserRuleContext<'input,ShiftSourceStateListContextExt<'input>>;

pub trait ShiftSourceStateListContextAttrs<'input>: LibSLParserContext<'input>{
	/// Retrieves first TerminalNode corresponding to token L_PAREN
	/// Returns `None` if there is no child corresponding to token L_PAREN
	fn L_PAREN(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(L_PAREN, 0)
	}
	/// Retrieves first TerminalNode corresponding to token R_PAREN
	/// Returns `None` if there is no child corresponding to token R_PAREN
	fn R_PAREN(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(R_PAREN, 0)
	}
	fn identList(&self) -> Option<Rc<IdentListContextAll<'input>>> where Self:Sized{
		self.child_of_type(0)
	}
	/// Retrieves first TerminalNode corresponding to token COMMA
	/// Returns `None` if there is no child corresponding to token COMMA
	fn COMMA(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(COMMA, 0)
	}
}

impl<'input> ShiftSourceStateListContextAttrs<'input> for ShiftSourceStateListContext<'input>{}

pub struct ShiftSourceStateListContextExt<'input>{
	__base:ShiftSourceStateContextExt<'input>,
	pub states: Option<Rc<IdentListContextAll<'input>>>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{ShiftSourceStateListContextExt<'a>}

impl<'input> LibSLParserContext<'input> for ShiftSourceStateListContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for ShiftSourceStateListContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_ShiftSourceStateList(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_ShiftSourceStateList(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for ShiftSourceStateListContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_shiftSourceState }
	//fn type_rule_index() -> usize where Self: Sized { RULE_shiftSourceState }
}

impl<'input> Borrow<ShiftSourceStateContextExt<'input>> for ShiftSourceStateListContext<'input>{
	fn borrow(&self) -> &ShiftSourceStateContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<ShiftSourceStateContextExt<'input>> for ShiftSourceStateListContext<'input>{
	fn borrow_mut(&mut self) -> &mut ShiftSourceStateContextExt<'input> { &mut self.__base }
}

impl<'input> ShiftSourceStateContextAttrs<'input> for ShiftSourceStateListContext<'input> {}

impl<'input> ShiftSourceStateListContextExt<'input>{
	fn new(ctx: &dyn ShiftSourceStateContextAttrs<'input>) -> Rc<ShiftSourceStateContextAll<'input>>  {
		Rc::new(
			ShiftSourceStateContextAll::ShiftSourceStateListContext(
				BaseParserRuleContext::copy_from(ctx,ShiftSourceStateListContextExt{
        			states:None, 
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

impl<'input, I, H> LibSLParser<'input, I, H>
where
    I: TokenStream<'input, TF = LocalTokenFactory<'input> > + TidAble<'input>,
    H: ErrorStrategy<'input,BaseParserType<'input,I>>
{
	pub fn shiftSourceState(&mut self,)
	-> Result<Rc<ShiftSourceStateContextAll<'input>>,ANTLRError> {
		let mut recog = self;
		let _parentctx = recog.ctx.take();
		let mut _localctx = ShiftSourceStateContextExt::new(_parentctx.clone(), recog.base.get_state());
        recog.base.enter_rule(_localctx.clone(), 80, RULE_shiftSourceState);
        let mut _localctx: Rc<ShiftSourceStateContextAll> = _localctx;
		let mut _la: isize = -1;
		let result: Result<(), ANTLRError> = (|| {

			recog.base.set_state(679);
			recog.err_handler.sync(&mut recog.base)?;
			match recog.base.input.la(1) {
			 IMPLEMENTS | STATIC | PURE | Identifier 
				=> {
					let tmp = ShiftSourceStateShorthandContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 1);
					_localctx = tmp;
					{
					/*InvokeRule ident*/
					recog.base.set_state(670);
					recog.ident()?;

					}
				}

			 L_PAREN 
				=> {
					let tmp = ShiftSourceStateListContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 2);
					_localctx = tmp;
					{
					recog.base.set_state(671);
					recog.base.match_token(L_PAREN,&mut recog.err_handler)?;

					recog.base.set_state(676);
					recog.err_handler.sync(&mut recog.base)?;
					_la = recog.base.input.la(1);
					if ((((_la - 86)) & !0x3f) == 0 && ((1usize << (_la - 86)) & 519) != 0) {
						{
						/*InvokeRule identList*/
						recog.base.set_state(672);
						let tmp = recog.identList()?;
						if let ShiftSourceStateContextAll::ShiftSourceStateListContext(ctx) = cast_mut::<_,ShiftSourceStateContextAll >(&mut _localctx){
						ctx.states = Some(tmp.clone()); } else {unreachable!("cant cast");}  

						recog.base.set_state(674);
						recog.err_handler.sync(&mut recog.base)?;
						_la = recog.base.input.la(1);
						if _la==COMMA {
							{
							recog.base.set_state(673);
							recog.base.match_token(COMMA,&mut recog.err_handler)?;

							}
						}

						}
					}

					recog.base.set_state(678);
					recog.base.match_token(R_PAREN,&mut recog.err_handler)?;

					}
				}

				_ => Err(ANTLRError::NoAltError(NoViableAltError::new(&mut recog.base)))?
			}
			Ok(())
		})();
		match result {
		Ok(_)=>{},
        Err(e @ ANTLRError::FallThrough(_)) => return Err(e),
		Err(ref re) => {
				//_localctx.exception = re;
				recog.err_handler.report_error(&mut recog.base, re);
				recog.err_handler.recover(&mut recog.base, re)?;
			}
		}
		recog.base.exit_rule();

		Ok(_localctx)
	}
}
//------------------- shiftBy ----------------
#[derive(Debug)]
pub enum ShiftByContextAll<'input>{
	ShiftByListContext(ShiftByListContext<'input>),
	ShiftByShorthandContext(ShiftByShorthandContext<'input>),
Error(ShiftByContext<'input>)
}
antlr_rust::tid!{ShiftByContextAll<'a>}

impl<'input> antlr_rust::parser_rule_context::DerefSeal for ShiftByContextAll<'input>{}

impl<'input> LibSLParserContext<'input> for ShiftByContextAll<'input>{}

impl<'input> Deref for ShiftByContextAll<'input>{
	type Target = dyn ShiftByContextAttrs<'input> + 'input;
	fn deref(&self) -> &Self::Target{
		use ShiftByContextAll::*;
		match self{
			ShiftByListContext(inner) => inner,
			ShiftByShorthandContext(inner) => inner,
Error(inner) => inner
		}
	}
}
impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for ShiftByContextAll<'input>{
    fn enter(&self, listener: &mut (dyn LibSLParserListener<'input> + 'a)) { self.deref().enter(listener) }
    fn exit(&self, listener: &mut (dyn LibSLParserListener<'input> + 'a)) { self.deref().exit(listener) }
}



pub type ShiftByContext<'input> = BaseParserRuleContext<'input,ShiftByContextExt<'input>>;

#[derive(Clone)]
pub struct ShiftByContextExt<'input>{
ph:PhantomData<&'input str>
}

impl<'input> LibSLParserContext<'input> for ShiftByContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for ShiftByContext<'input>{
}

impl<'input> CustomRuleContext<'input> for ShiftByContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_shiftBy }
	//fn type_rule_index() -> usize where Self: Sized { RULE_shiftBy }
}
antlr_rust::tid!{ShiftByContextExt<'a>}

impl<'input> ShiftByContextExt<'input>{
	fn new(parent: Option<Rc<dyn LibSLParserContext<'input> + 'input > >, invoking_state: isize) -> Rc<ShiftByContextAll<'input>> {
		Rc::new(
		ShiftByContextAll::Error(
			BaseParserRuleContext::new_parser_ctx(parent, invoking_state,ShiftByContextExt{
				ph:PhantomData
			}),
		)
		)
	}
}

pub trait ShiftByContextAttrs<'input>: LibSLParserContext<'input> + BorrowMut<ShiftByContextExt<'input>>{


}

impl<'input> ShiftByContextAttrs<'input> for ShiftByContext<'input>{}

pub type ShiftByListContext<'input> = BaseParserRuleContext<'input,ShiftByListContextExt<'input>>;

pub trait ShiftByListContextAttrs<'input>: LibSLParserContext<'input>{
	/// Retrieves first TerminalNode corresponding to token L_BRACKET
	/// Returns `None` if there is no child corresponding to token L_BRACKET
	fn L_BRACKET(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(L_BRACKET, 0)
	}
	/// Retrieves first TerminalNode corresponding to token R_BRACKET
	/// Returns `None` if there is no child corresponding to token R_BRACKET
	fn R_BRACKET(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(R_BRACKET, 0)
	}
	fn functionSignatureList(&self) -> Option<Rc<FunctionSignatureListContextAll<'input>>> where Self:Sized{
		self.child_of_type(0)
	}
	/// Retrieves first TerminalNode corresponding to token COMMA
	/// Returns `None` if there is no child corresponding to token COMMA
	fn COMMA(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(COMMA, 0)
	}
}

impl<'input> ShiftByListContextAttrs<'input> for ShiftByListContext<'input>{}

pub struct ShiftByListContextExt<'input>{
	__base:ShiftByContextExt<'input>,
	pub signatures: Option<Rc<FunctionSignatureListContextAll<'input>>>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{ShiftByListContextExt<'a>}

impl<'input> LibSLParserContext<'input> for ShiftByListContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for ShiftByListContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_ShiftByList(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_ShiftByList(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for ShiftByListContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_shiftBy }
	//fn type_rule_index() -> usize where Self: Sized { RULE_shiftBy }
}

impl<'input> Borrow<ShiftByContextExt<'input>> for ShiftByListContext<'input>{
	fn borrow(&self) -> &ShiftByContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<ShiftByContextExt<'input>> for ShiftByListContext<'input>{
	fn borrow_mut(&mut self) -> &mut ShiftByContextExt<'input> { &mut self.__base }
}

impl<'input> ShiftByContextAttrs<'input> for ShiftByListContext<'input> {}

impl<'input> ShiftByListContextExt<'input>{
	fn new(ctx: &dyn ShiftByContextAttrs<'input>) -> Rc<ShiftByContextAll<'input>>  {
		Rc::new(
			ShiftByContextAll::ShiftByListContext(
				BaseParserRuleContext::copy_from(ctx,ShiftByListContextExt{
        			signatures:None, 
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type ShiftByShorthandContext<'input> = BaseParserRuleContext<'input,ShiftByShorthandContextExt<'input>>;

pub trait ShiftByShorthandContextAttrs<'input>: LibSLParserContext<'input>{
	fn functionSignature(&self) -> Option<Rc<FunctionSignatureContextAll<'input>>> where Self:Sized{
		self.child_of_type(0)
	}
}

impl<'input> ShiftByShorthandContextAttrs<'input> for ShiftByShorthandContext<'input>{}

pub struct ShiftByShorthandContextExt<'input>{
	__base:ShiftByContextExt<'input>,
	pub signature: Option<Rc<FunctionSignatureContextAll<'input>>>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{ShiftByShorthandContextExt<'a>}

impl<'input> LibSLParserContext<'input> for ShiftByShorthandContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for ShiftByShorthandContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_ShiftByShorthand(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_ShiftByShorthand(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for ShiftByShorthandContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_shiftBy }
	//fn type_rule_index() -> usize where Self: Sized { RULE_shiftBy }
}

impl<'input> Borrow<ShiftByContextExt<'input>> for ShiftByShorthandContext<'input>{
	fn borrow(&self) -> &ShiftByContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<ShiftByContextExt<'input>> for ShiftByShorthandContext<'input>{
	fn borrow_mut(&mut self) -> &mut ShiftByContextExt<'input> { &mut self.__base }
}

impl<'input> ShiftByContextAttrs<'input> for ShiftByShorthandContext<'input> {}

impl<'input> ShiftByShorthandContextExt<'input>{
	fn new(ctx: &dyn ShiftByContextAttrs<'input>) -> Rc<ShiftByContextAll<'input>>  {
		Rc::new(
			ShiftByContextAll::ShiftByShorthandContext(
				BaseParserRuleContext::copy_from(ctx,ShiftByShorthandContextExt{
        			signature:None, 
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

impl<'input, I, H> LibSLParser<'input, I, H>
where
    I: TokenStream<'input, TF = LocalTokenFactory<'input> > + TidAble<'input>,
    H: ErrorStrategy<'input,BaseParserType<'input,I>>
{
	pub fn shiftBy(&mut self,)
	-> Result<Rc<ShiftByContextAll<'input>>,ANTLRError> {
		let mut recog = self;
		let _parentctx = recog.ctx.take();
		let mut _localctx = ShiftByContextExt::new(_parentctx.clone(), recog.base.get_state());
        recog.base.enter_rule(_localctx.clone(), 82, RULE_shiftBy);
        let mut _localctx: Rc<ShiftByContextAll> = _localctx;
		let mut _la: isize = -1;
		let result: Result<(), ANTLRError> = (|| {

			recog.base.set_state(690);
			recog.err_handler.sync(&mut recog.base)?;
			match recog.base.input.la(1) {
			 IMPLEMENTS | STATIC | PURE | Identifier 
				=> {
					let tmp = ShiftByShorthandContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 1);
					_localctx = tmp;
					{
					/*InvokeRule functionSignature*/
					recog.base.set_state(681);
					let tmp = recog.functionSignature()?;
					if let ShiftByContextAll::ShiftByShorthandContext(ctx) = cast_mut::<_,ShiftByContextAll >(&mut _localctx){
					ctx.signature = Some(tmp.clone()); } else {unreachable!("cant cast");}  

					}
				}

			 L_BRACKET 
				=> {
					let tmp = ShiftByListContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 2);
					_localctx = tmp;
					{
					recog.base.set_state(682);
					recog.base.match_token(L_BRACKET,&mut recog.err_handler)?;

					recog.base.set_state(687);
					recog.err_handler.sync(&mut recog.base)?;
					_la = recog.base.input.la(1);
					if ((((_la - 86)) & !0x3f) == 0 && ((1usize << (_la - 86)) & 519) != 0) {
						{
						/*InvokeRule functionSignatureList*/
						recog.base.set_state(683);
						let tmp = recog.functionSignatureList()?;
						if let ShiftByContextAll::ShiftByListContext(ctx) = cast_mut::<_,ShiftByContextAll >(&mut _localctx){
						ctx.signatures = Some(tmp.clone()); } else {unreachable!("cant cast");}  

						recog.base.set_state(685);
						recog.err_handler.sync(&mut recog.base)?;
						_la = recog.base.input.la(1);
						if _la==COMMA {
							{
							recog.base.set_state(684);
							recog.base.match_token(COMMA,&mut recog.err_handler)?;

							}
						}

						}
					}

					recog.base.set_state(689);
					recog.base.match_token(R_BRACKET,&mut recog.err_handler)?;

					}
				}

				_ => Err(ANTLRError::NoAltError(NoViableAltError::new(&mut recog.base)))?
			}
			Ok(())
		})();
		match result {
		Ok(_)=>{},
        Err(e @ ANTLRError::FallThrough(_)) => return Err(e),
		Err(ref re) => {
				//_localctx.exception = re;
				recog.err_handler.report_error(&mut recog.base, re);
				recog.err_handler.recover(&mut recog.base, re)?;
			}
		}
		recog.base.exit_rule();

		Ok(_localctx)
	}
}
//------------------- functionSignatureList ----------------
pub type FunctionSignatureListContextAll<'input> = FunctionSignatureListContext<'input>;


pub type FunctionSignatureListContext<'input> = BaseParserRuleContext<'input,FunctionSignatureListContextExt<'input>>;

#[derive(Clone)]
pub struct FunctionSignatureListContextExt<'input>{
	pub functionSignature: Option<Rc<FunctionSignatureContextAll<'input>>>,
	pub signatures:Vec<Rc<FunctionSignatureContextAll<'input>>>,
ph:PhantomData<&'input str>
}

impl<'input> LibSLParserContext<'input> for FunctionSignatureListContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for FunctionSignatureListContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_functionSignatureList(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_functionSignatureList(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for FunctionSignatureListContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_functionSignatureList }
	//fn type_rule_index() -> usize where Self: Sized { RULE_functionSignatureList }
}
antlr_rust::tid!{FunctionSignatureListContextExt<'a>}

impl<'input> FunctionSignatureListContextExt<'input>{
	fn new(parent: Option<Rc<dyn LibSLParserContext<'input> + 'input > >, invoking_state: isize) -> Rc<FunctionSignatureListContextAll<'input>> {
		Rc::new(
			BaseParserRuleContext::new_parser_ctx(parent, invoking_state,FunctionSignatureListContextExt{
				functionSignature: None, 
				signatures: Vec::new(), 
				ph:PhantomData
			}),
		)
	}
}

pub trait FunctionSignatureListContextAttrs<'input>: LibSLParserContext<'input> + BorrowMut<FunctionSignatureListContextExt<'input>>{

fn functionSignature_all(&self) ->  Vec<Rc<FunctionSignatureContextAll<'input>>> where Self:Sized{
	self.children_of_type()
}
fn functionSignature(&self, i: usize) -> Option<Rc<FunctionSignatureContextAll<'input>>> where Self:Sized{
	self.child_of_type(i)
}
/// Retrieves all `TerminalNode`s corresponding to token COMMA in current rule
fn COMMA_all(&self) -> Vec<Rc<TerminalNode<'input,LibSLParserContextType>>>  where Self:Sized{
	self.get_tokens(COMMA)
}
/// Retrieves 'i's TerminalNode corresponding to token COMMA, starting from 0.
/// Returns `None` if number of children corresponding to token COMMA is less or equal than `i`.
fn COMMA(&self, i: usize) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(COMMA, i)
}

}

impl<'input> FunctionSignatureListContextAttrs<'input> for FunctionSignatureListContext<'input>{}

impl<'input, I, H> LibSLParser<'input, I, H>
where
    I: TokenStream<'input, TF = LocalTokenFactory<'input> > + TidAble<'input>,
    H: ErrorStrategy<'input,BaseParserType<'input,I>>
{
	pub fn functionSignatureList(&mut self,)
	-> Result<Rc<FunctionSignatureListContextAll<'input>>,ANTLRError> {
		let mut recog = self;
		let _parentctx = recog.ctx.take();
		let mut _localctx = FunctionSignatureListContextExt::new(_parentctx.clone(), recog.base.get_state());
        recog.base.enter_rule(_localctx.clone(), 84, RULE_functionSignatureList);
        let mut _localctx: Rc<FunctionSignatureListContextAll> = _localctx;
		let result: Result<(), ANTLRError> = (|| {

			let mut _alt: isize;
			//recog.base.enter_outer_alt(_localctx.clone(), 1);
			recog.base.enter_outer_alt(None, 1);
			{
			/*InvokeRule functionSignature*/
			recog.base.set_state(692);
			let tmp = recog.functionSignature()?;
			 cast_mut::<_,FunctionSignatureListContext >(&mut _localctx).functionSignature = Some(tmp.clone());
			  

			let temp =  cast_mut::<_,FunctionSignatureListContext >(&mut _localctx).functionSignature.clone().unwrap()
			 ;
			 cast_mut::<_,FunctionSignatureListContext >(&mut _localctx).signatures.push(temp);
			  
			recog.base.set_state(697);
			recog.err_handler.sync(&mut recog.base)?;
			_alt = recog.interpreter.adaptive_predict(79,&mut recog.base)?;
			while { _alt!=2 && _alt!=INVALID_ALT } {
				if _alt==1 {
					{
					{
					recog.base.set_state(693);
					recog.base.match_token(COMMA,&mut recog.err_handler)?;

					/*InvokeRule functionSignature*/
					recog.base.set_state(694);
					let tmp = recog.functionSignature()?;
					 cast_mut::<_,FunctionSignatureListContext >(&mut _localctx).functionSignature = Some(tmp.clone());
					  

					let temp =  cast_mut::<_,FunctionSignatureListContext >(&mut _localctx).functionSignature.clone().unwrap()
					 ;
					 cast_mut::<_,FunctionSignatureListContext >(&mut _localctx).signatures.push(temp);
					  
					}
					} 
				}
				recog.base.set_state(699);
				recog.err_handler.sync(&mut recog.base)?;
				_alt = recog.interpreter.adaptive_predict(79,&mut recog.base)?;
			}
			}
			Ok(())
		})();
		match result {
		Ok(_)=>{},
        Err(e @ ANTLRError::FallThrough(_)) => return Err(e),
		Err(ref re) => {
				//_localctx.exception = re;
				recog.err_handler.report_error(&mut recog.base, re);
				recog.err_handler.recover(&mut recog.base, re)?;
			}
		}
		recog.base.exit_rule();

		Ok(_localctx)
	}
}
//------------------- functionSignature ----------------
#[derive(Debug)]
pub enum FunctionSignatureContextAll<'input>{
	FunctionSignatureQualifiedContext(FunctionSignatureQualifiedContext<'input>),
	FunctionSignatureShorthandContext(FunctionSignatureShorthandContext<'input>),
Error(FunctionSignatureContext<'input>)
}
antlr_rust::tid!{FunctionSignatureContextAll<'a>}

impl<'input> antlr_rust::parser_rule_context::DerefSeal for FunctionSignatureContextAll<'input>{}

impl<'input> LibSLParserContext<'input> for FunctionSignatureContextAll<'input>{}

impl<'input> Deref for FunctionSignatureContextAll<'input>{
	type Target = dyn FunctionSignatureContextAttrs<'input> + 'input;
	fn deref(&self) -> &Self::Target{
		use FunctionSignatureContextAll::*;
		match self{
			FunctionSignatureQualifiedContext(inner) => inner,
			FunctionSignatureShorthandContext(inner) => inner,
Error(inner) => inner
		}
	}
}
impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for FunctionSignatureContextAll<'input>{
    fn enter(&self, listener: &mut (dyn LibSLParserListener<'input> + 'a)) { self.deref().enter(listener) }
    fn exit(&self, listener: &mut (dyn LibSLParserListener<'input> + 'a)) { self.deref().exit(listener) }
}



pub type FunctionSignatureContext<'input> = BaseParserRuleContext<'input,FunctionSignatureContextExt<'input>>;

#[derive(Clone)]
pub struct FunctionSignatureContextExt<'input>{
ph:PhantomData<&'input str>
}

impl<'input> LibSLParserContext<'input> for FunctionSignatureContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for FunctionSignatureContext<'input>{
}

impl<'input> CustomRuleContext<'input> for FunctionSignatureContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_functionSignature }
	//fn type_rule_index() -> usize where Self: Sized { RULE_functionSignature }
}
antlr_rust::tid!{FunctionSignatureContextExt<'a>}

impl<'input> FunctionSignatureContextExt<'input>{
	fn new(parent: Option<Rc<dyn LibSLParserContext<'input> + 'input > >, invoking_state: isize) -> Rc<FunctionSignatureContextAll<'input>> {
		Rc::new(
		FunctionSignatureContextAll::Error(
			BaseParserRuleContext::new_parser_ctx(parent, invoking_state,FunctionSignatureContextExt{
				ph:PhantomData
			}),
		)
		)
	}
}

pub trait FunctionSignatureContextAttrs<'input>: LibSLParserContext<'input> + BorrowMut<FunctionSignatureContextExt<'input>>{


}

impl<'input> FunctionSignatureContextAttrs<'input> for FunctionSignatureContext<'input>{}

pub type FunctionSignatureQualifiedContext<'input> = BaseParserRuleContext<'input,FunctionSignatureQualifiedContextExt<'input>>;

pub trait FunctionSignatureQualifiedContextAttrs<'input>: LibSLParserContext<'input>{
	/// Retrieves first TerminalNode corresponding to token L_PAREN
	/// Returns `None` if there is no child corresponding to token L_PAREN
	fn L_PAREN(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(L_PAREN, 0)
	}
	/// Retrieves first TerminalNode corresponding to token R_PAREN
	/// Returns `None` if there is no child corresponding to token R_PAREN
	fn R_PAREN(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(R_PAREN, 0)
	}
	fn ident(&self) -> Option<Rc<IdentContextAll<'input>>> where Self:Sized{
		self.child_of_type(0)
	}
	fn typeExprList(&self) -> Option<Rc<TypeExprListContextAll<'input>>> where Self:Sized{
		self.child_of_type(0)
	}
	/// Retrieves first TerminalNode corresponding to token COMMA
	/// Returns `None` if there is no child corresponding to token COMMA
	fn COMMA(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(COMMA, 0)
	}
}

impl<'input> FunctionSignatureQualifiedContextAttrs<'input> for FunctionSignatureQualifiedContext<'input>{}

pub struct FunctionSignatureQualifiedContextExt<'input>{
	__base:FunctionSignatureContextExt<'input>,
	pub name: Option<Rc<IdentContextAll<'input>>>,
	pub params: Option<Rc<TypeExprListContextAll<'input>>>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{FunctionSignatureQualifiedContextExt<'a>}

impl<'input> LibSLParserContext<'input> for FunctionSignatureQualifiedContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for FunctionSignatureQualifiedContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_FunctionSignatureQualified(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_FunctionSignatureQualified(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for FunctionSignatureQualifiedContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_functionSignature }
	//fn type_rule_index() -> usize where Self: Sized { RULE_functionSignature }
}

impl<'input> Borrow<FunctionSignatureContextExt<'input>> for FunctionSignatureQualifiedContext<'input>{
	fn borrow(&self) -> &FunctionSignatureContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<FunctionSignatureContextExt<'input>> for FunctionSignatureQualifiedContext<'input>{
	fn borrow_mut(&mut self) -> &mut FunctionSignatureContextExt<'input> { &mut self.__base }
}

impl<'input> FunctionSignatureContextAttrs<'input> for FunctionSignatureQualifiedContext<'input> {}

impl<'input> FunctionSignatureQualifiedContextExt<'input>{
	fn new(ctx: &dyn FunctionSignatureContextAttrs<'input>) -> Rc<FunctionSignatureContextAll<'input>>  {
		Rc::new(
			FunctionSignatureContextAll::FunctionSignatureQualifiedContext(
				BaseParserRuleContext::copy_from(ctx,FunctionSignatureQualifiedContextExt{
        			name:None, params:None, 
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type FunctionSignatureShorthandContext<'input> = BaseParserRuleContext<'input,FunctionSignatureShorthandContextExt<'input>>;

pub trait FunctionSignatureShorthandContextAttrs<'input>: LibSLParserContext<'input>{
	fn ident(&self) -> Option<Rc<IdentContextAll<'input>>> where Self:Sized{
		self.child_of_type(0)
	}
}

impl<'input> FunctionSignatureShorthandContextAttrs<'input> for FunctionSignatureShorthandContext<'input>{}

pub struct FunctionSignatureShorthandContextExt<'input>{
	__base:FunctionSignatureContextExt<'input>,
	pub name: Option<Rc<IdentContextAll<'input>>>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{FunctionSignatureShorthandContextExt<'a>}

impl<'input> LibSLParserContext<'input> for FunctionSignatureShorthandContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for FunctionSignatureShorthandContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_FunctionSignatureShorthand(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_FunctionSignatureShorthand(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for FunctionSignatureShorthandContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_functionSignature }
	//fn type_rule_index() -> usize where Self: Sized { RULE_functionSignature }
}

impl<'input> Borrow<FunctionSignatureContextExt<'input>> for FunctionSignatureShorthandContext<'input>{
	fn borrow(&self) -> &FunctionSignatureContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<FunctionSignatureContextExt<'input>> for FunctionSignatureShorthandContext<'input>{
	fn borrow_mut(&mut self) -> &mut FunctionSignatureContextExt<'input> { &mut self.__base }
}

impl<'input> FunctionSignatureContextAttrs<'input> for FunctionSignatureShorthandContext<'input> {}

impl<'input> FunctionSignatureShorthandContextExt<'input>{
	fn new(ctx: &dyn FunctionSignatureContextAttrs<'input>) -> Rc<FunctionSignatureContextAll<'input>>  {
		Rc::new(
			FunctionSignatureContextAll::FunctionSignatureShorthandContext(
				BaseParserRuleContext::copy_from(ctx,FunctionSignatureShorthandContextExt{
        			name:None, 
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

impl<'input, I, H> LibSLParser<'input, I, H>
where
    I: TokenStream<'input, TF = LocalTokenFactory<'input> > + TidAble<'input>,
    H: ErrorStrategy<'input,BaseParserType<'input,I>>
{
	pub fn functionSignature(&mut self,)
	-> Result<Rc<FunctionSignatureContextAll<'input>>,ANTLRError> {
		let mut recog = self;
		let _parentctx = recog.ctx.take();
		let mut _localctx = FunctionSignatureContextExt::new(_parentctx.clone(), recog.base.get_state());
        recog.base.enter_rule(_localctx.clone(), 86, RULE_functionSignature);
        let mut _localctx: Rc<FunctionSignatureContextAll> = _localctx;
		let mut _la: isize = -1;
		let result: Result<(), ANTLRError> = (|| {

			recog.base.set_state(711);
			recog.err_handler.sync(&mut recog.base)?;
			match  recog.interpreter.adaptive_predict(82,&mut recog.base)? {
				1 =>{
					let tmp = FunctionSignatureShorthandContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 1);
					_localctx = tmp;
					{
					/*InvokeRule ident*/
					recog.base.set_state(700);
					let tmp = recog.ident()?;
					if let FunctionSignatureContextAll::FunctionSignatureShorthandContext(ctx) = cast_mut::<_,FunctionSignatureContextAll >(&mut _localctx){
					ctx.name = Some(tmp.clone()); } else {unreachable!("cant cast");}  

					}
				}
			,
				2 =>{
					let tmp = FunctionSignatureQualifiedContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 2);
					_localctx = tmp;
					{
					/*InvokeRule ident*/
					recog.base.set_state(701);
					let tmp = recog.ident()?;
					if let FunctionSignatureContextAll::FunctionSignatureQualifiedContext(ctx) = cast_mut::<_,FunctionSignatureContextAll >(&mut _localctx){
					ctx.name = Some(tmp.clone()); } else {unreachable!("cant cast");}  

					recog.base.set_state(702);
					recog.base.match_token(L_PAREN,&mut recog.err_handler)?;

					recog.base.set_state(707);
					recog.err_handler.sync(&mut recog.base)?;
					_la = recog.base.input.la(1);
					if _la==L_PAREN || _la==ASTERISK || ((((_la - 73)) & !0x3f) == 0 && ((1usize << (_la - 73)) & 32039171) != 0) {
						{
						/*InvokeRule typeExprList*/
						recog.base.set_state(703);
						let tmp = recog.typeExprList()?;
						if let FunctionSignatureContextAll::FunctionSignatureQualifiedContext(ctx) = cast_mut::<_,FunctionSignatureContextAll >(&mut _localctx){
						ctx.params = Some(tmp.clone()); } else {unreachable!("cant cast");}  

						recog.base.set_state(705);
						recog.err_handler.sync(&mut recog.base)?;
						_la = recog.base.input.la(1);
						if _la==COMMA {
							{
							recog.base.set_state(704);
							recog.base.match_token(COMMA,&mut recog.err_handler)?;

							}
						}

						}
					}

					recog.base.set_state(709);
					recog.base.match_token(R_PAREN,&mut recog.err_handler)?;

					}
				}

				_ => {}
			}
			Ok(())
		})();
		match result {
		Ok(_)=>{},
        Err(e @ ANTLRError::FallThrough(_)) => return Err(e),
		Err(ref re) => {
				//_localctx.exception = re;
				recog.err_handler.report_error(&mut recog.base, re);
				recog.err_handler.recover(&mut recog.base, re)?;
			}
		}
		recog.base.exit_rule();

		Ok(_localctx)
	}
}
//------------------- constructorDecl ----------------
pub type ConstructorDeclContextAll<'input> = ConstructorDeclContext<'input>;


pub type ConstructorDeclContext<'input> = BaseParserRuleContext<'input,ConstructorDeclContextExt<'input>>;

#[derive(Clone)]
pub struct ConstructorDeclContextExt<'input>{
	pub annotation: Option<Rc<AnnotationContextAll<'input>>>,
	pub annotations:Vec<Rc<AnnotationContextAll<'input>>>,
	pub method: Option<Rc<MethodSpecContextAll<'input>>>,
	pub name: Option<Rc<IdentContextAll<'input>>>,
	pub params: Option<Rc<FunctionParamListContextAll<'input>>>,
	pub retType: Option<Rc<TypeExprContextAll<'input>>>,
	pub def: Option<Rc<FunctionDefContextAll<'input>>>,
ph:PhantomData<&'input str>
}

impl<'input> LibSLParserContext<'input> for ConstructorDeclContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for ConstructorDeclContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_constructorDecl(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_constructorDecl(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for ConstructorDeclContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_constructorDecl }
	//fn type_rule_index() -> usize where Self: Sized { RULE_constructorDecl }
}
antlr_rust::tid!{ConstructorDeclContextExt<'a>}

impl<'input> ConstructorDeclContextExt<'input>{
	fn new(parent: Option<Rc<dyn LibSLParserContext<'input> + 'input > >, invoking_state: isize) -> Rc<ConstructorDeclContextAll<'input>> {
		Rc::new(
			BaseParserRuleContext::new_parser_ctx(parent, invoking_state,ConstructorDeclContextExt{
				annotation: None, method: None, name: None, params: None, retType: None, def: None, 
				annotations: Vec::new(), 
				ph:PhantomData
			}),
		)
	}
}

pub trait ConstructorDeclContextAttrs<'input>: LibSLParserContext<'input> + BorrowMut<ConstructorDeclContextExt<'input>>{

/// Retrieves first TerminalNode corresponding to token CONSTRUCTOR
/// Returns `None` if there is no child corresponding to token CONSTRUCTOR
fn CONSTRUCTOR(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(CONSTRUCTOR, 0)
}
/// Retrieves first TerminalNode corresponding to token L_PAREN
/// Returns `None` if there is no child corresponding to token L_PAREN
fn L_PAREN(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(L_PAREN, 0)
}
/// Retrieves first TerminalNode corresponding to token R_PAREN
/// Returns `None` if there is no child corresponding to token R_PAREN
fn R_PAREN(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(R_PAREN, 0)
}
fn functionDef(&self) -> Option<Rc<FunctionDefContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}
/// Retrieves first TerminalNode corresponding to token COLON
/// Returns `None` if there is no child corresponding to token COLON
fn COLON(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(COLON, 0)
}
fn annotation_all(&self) ->  Vec<Rc<AnnotationContextAll<'input>>> where Self:Sized{
	self.children_of_type()
}
fn annotation(&self, i: usize) -> Option<Rc<AnnotationContextAll<'input>>> where Self:Sized{
	self.child_of_type(i)
}
fn methodSpec(&self) -> Option<Rc<MethodSpecContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}
fn ident(&self) -> Option<Rc<IdentContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}
fn functionParamList(&self) -> Option<Rc<FunctionParamListContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}
fn typeExpr(&self) -> Option<Rc<TypeExprContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}
/// Retrieves first TerminalNode corresponding to token COMMA
/// Returns `None` if there is no child corresponding to token COMMA
fn COMMA(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(COMMA, 0)
}

}

impl<'input> ConstructorDeclContextAttrs<'input> for ConstructorDeclContext<'input>{}

impl<'input, I, H> LibSLParser<'input, I, H>
where
    I: TokenStream<'input, TF = LocalTokenFactory<'input> > + TidAble<'input>,
    H: ErrorStrategy<'input,BaseParserType<'input,I>>
{
	pub fn constructorDecl(&mut self,)
	-> Result<Rc<ConstructorDeclContextAll<'input>>,ANTLRError> {
		let mut recog = self;
		let _parentctx = recog.ctx.take();
		let mut _localctx = ConstructorDeclContextExt::new(_parentctx.clone(), recog.base.get_state());
        recog.base.enter_rule(_localctx.clone(), 88, RULE_constructorDecl);
        let mut _localctx: Rc<ConstructorDeclContextAll> = _localctx;
		let mut _la: isize = -1;
		let result: Result<(), ANTLRError> = (|| {

			//recog.base.enter_outer_alt(_localctx.clone(), 1);
			recog.base.enter_outer_alt(None, 1);
			{
			recog.base.set_state(716);
			recog.err_handler.sync(&mut recog.base)?;
			_la = recog.base.input.la(1);
			while _la==AT {
				{
				{
				/*InvokeRule annotation*/
				recog.base.set_state(713);
				let tmp = recog.annotation()?;
				 cast_mut::<_,ConstructorDeclContext >(&mut _localctx).annotation = Some(tmp.clone());
				  

				let temp =  cast_mut::<_,ConstructorDeclContext >(&mut _localctx).annotation.clone().unwrap()
				 ;
				 cast_mut::<_,ConstructorDeclContext >(&mut _localctx).annotations.push(temp);
				  
				}
				}
				recog.base.set_state(718);
				recog.err_handler.sync(&mut recog.base)?;
				_la = recog.base.input.la(1);
			}
			recog.base.set_state(719);
			recog.base.match_token(CONSTRUCTOR,&mut recog.err_handler)?;

			recog.base.set_state(721);
			recog.err_handler.sync(&mut recog.base)?;
			_la = recog.base.input.la(1);
			if _la==ASTERISK {
				{
				/*InvokeRule methodSpec*/
				recog.base.set_state(720);
				let tmp = recog.methodSpec()?;
				 cast_mut::<_,ConstructorDeclContext >(&mut _localctx).method = Some(tmp.clone());
				  

				}
			}

			recog.base.set_state(724);
			recog.err_handler.sync(&mut recog.base)?;
			_la = recog.base.input.la(1);
			if ((((_la - 86)) & !0x3f) == 0 && ((1usize << (_la - 86)) & 519) != 0) {
				{
				/*InvokeRule ident*/
				recog.base.set_state(723);
				let tmp = recog.ident()?;
				 cast_mut::<_,ConstructorDeclContext >(&mut _localctx).name = Some(tmp.clone());
				  

				}
			}

			recog.base.set_state(726);
			recog.base.match_token(L_PAREN,&mut recog.err_handler)?;

			recog.base.set_state(731);
			recog.err_handler.sync(&mut recog.base)?;
			_la = recog.base.input.la(1);
			if ((((_la - 86)) & !0x3f) == 0 && ((1usize << (_la - 86)) & 647) != 0) {
				{
				/*InvokeRule functionParamList*/
				recog.base.set_state(727);
				let tmp = recog.functionParamList()?;
				 cast_mut::<_,ConstructorDeclContext >(&mut _localctx).params = Some(tmp.clone());
				  

				recog.base.set_state(729);
				recog.err_handler.sync(&mut recog.base)?;
				_la = recog.base.input.la(1);
				if _la==COMMA {
					{
					recog.base.set_state(728);
					recog.base.match_token(COMMA,&mut recog.err_handler)?;

					}
				}

				}
			}

			recog.base.set_state(733);
			recog.base.match_token(R_PAREN,&mut recog.err_handler)?;

			recog.base.set_state(736);
			recog.err_handler.sync(&mut recog.base)?;
			_la = recog.base.input.la(1);
			if _la==COLON {
				{
				recog.base.set_state(734);
				recog.base.match_token(COLON,&mut recog.err_handler)?;

				/*InvokeRule typeExpr*/
				recog.base.set_state(735);
				let tmp = recog.typeExpr_rec(0)?;
				 cast_mut::<_,ConstructorDeclContext >(&mut _localctx).retType = Some(tmp.clone());
				  

				}
			}

			/*InvokeRule functionDef*/
			recog.base.set_state(738);
			let tmp = recog.functionDef()?;
			 cast_mut::<_,ConstructorDeclContext >(&mut _localctx).def = Some(tmp.clone());
			  

			}
			Ok(())
		})();
		match result {
		Ok(_)=>{},
        Err(e @ ANTLRError::FallThrough(_)) => return Err(e),
		Err(ref re) => {
				//_localctx.exception = re;
				recog.err_handler.report_error(&mut recog.base, re);
				recog.err_handler.recover(&mut recog.base, re)?;
			}
		}
		recog.base.exit_rule();

		Ok(_localctx)
	}
}
//------------------- destructorDecl ----------------
pub type DestructorDeclContextAll<'input> = DestructorDeclContext<'input>;


pub type DestructorDeclContext<'input> = BaseParserRuleContext<'input,DestructorDeclContextExt<'input>>;

#[derive(Clone)]
pub struct DestructorDeclContextExt<'input>{
	pub annotation: Option<Rc<AnnotationContextAll<'input>>>,
	pub annotations:Vec<Rc<AnnotationContextAll<'input>>>,
	pub method: Option<Rc<MethodSpecContextAll<'input>>>,
	pub name: Option<Rc<IdentContextAll<'input>>>,
	pub params: Option<Rc<FunctionParamListContextAll<'input>>>,
	pub retType: Option<Rc<TypeExprContextAll<'input>>>,
	pub def: Option<Rc<FunctionDefContextAll<'input>>>,
ph:PhantomData<&'input str>
}

impl<'input> LibSLParserContext<'input> for DestructorDeclContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for DestructorDeclContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_destructorDecl(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_destructorDecl(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for DestructorDeclContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_destructorDecl }
	//fn type_rule_index() -> usize where Self: Sized { RULE_destructorDecl }
}
antlr_rust::tid!{DestructorDeclContextExt<'a>}

impl<'input> DestructorDeclContextExt<'input>{
	fn new(parent: Option<Rc<dyn LibSLParserContext<'input> + 'input > >, invoking_state: isize) -> Rc<DestructorDeclContextAll<'input>> {
		Rc::new(
			BaseParserRuleContext::new_parser_ctx(parent, invoking_state,DestructorDeclContextExt{
				annotation: None, method: None, name: None, params: None, retType: None, def: None, 
				annotations: Vec::new(), 
				ph:PhantomData
			}),
		)
	}
}

pub trait DestructorDeclContextAttrs<'input>: LibSLParserContext<'input> + BorrowMut<DestructorDeclContextExt<'input>>{

/// Retrieves first TerminalNode corresponding to token DESTRUCTOR
/// Returns `None` if there is no child corresponding to token DESTRUCTOR
fn DESTRUCTOR(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(DESTRUCTOR, 0)
}
/// Retrieves first TerminalNode corresponding to token L_PAREN
/// Returns `None` if there is no child corresponding to token L_PAREN
fn L_PAREN(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(L_PAREN, 0)
}
/// Retrieves first TerminalNode corresponding to token R_PAREN
/// Returns `None` if there is no child corresponding to token R_PAREN
fn R_PAREN(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(R_PAREN, 0)
}
fn functionDef(&self) -> Option<Rc<FunctionDefContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}
/// Retrieves first TerminalNode corresponding to token COLON
/// Returns `None` if there is no child corresponding to token COLON
fn COLON(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(COLON, 0)
}
fn annotation_all(&self) ->  Vec<Rc<AnnotationContextAll<'input>>> where Self:Sized{
	self.children_of_type()
}
fn annotation(&self, i: usize) -> Option<Rc<AnnotationContextAll<'input>>> where Self:Sized{
	self.child_of_type(i)
}
fn methodSpec(&self) -> Option<Rc<MethodSpecContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}
fn ident(&self) -> Option<Rc<IdentContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}
fn functionParamList(&self) -> Option<Rc<FunctionParamListContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}
fn typeExpr(&self) -> Option<Rc<TypeExprContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}
/// Retrieves first TerminalNode corresponding to token COMMA
/// Returns `None` if there is no child corresponding to token COMMA
fn COMMA(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(COMMA, 0)
}

}

impl<'input> DestructorDeclContextAttrs<'input> for DestructorDeclContext<'input>{}

impl<'input, I, H> LibSLParser<'input, I, H>
where
    I: TokenStream<'input, TF = LocalTokenFactory<'input> > + TidAble<'input>,
    H: ErrorStrategy<'input,BaseParserType<'input,I>>
{
	pub fn destructorDecl(&mut self,)
	-> Result<Rc<DestructorDeclContextAll<'input>>,ANTLRError> {
		let mut recog = self;
		let _parentctx = recog.ctx.take();
		let mut _localctx = DestructorDeclContextExt::new(_parentctx.clone(), recog.base.get_state());
        recog.base.enter_rule(_localctx.clone(), 90, RULE_destructorDecl);
        let mut _localctx: Rc<DestructorDeclContextAll> = _localctx;
		let mut _la: isize = -1;
		let result: Result<(), ANTLRError> = (|| {

			//recog.base.enter_outer_alt(_localctx.clone(), 1);
			recog.base.enter_outer_alt(None, 1);
			{
			recog.base.set_state(743);
			recog.err_handler.sync(&mut recog.base)?;
			_la = recog.base.input.la(1);
			while _la==AT {
				{
				{
				/*InvokeRule annotation*/
				recog.base.set_state(740);
				let tmp = recog.annotation()?;
				 cast_mut::<_,DestructorDeclContext >(&mut _localctx).annotation = Some(tmp.clone());
				  

				let temp =  cast_mut::<_,DestructorDeclContext >(&mut _localctx).annotation.clone().unwrap()
				 ;
				 cast_mut::<_,DestructorDeclContext >(&mut _localctx).annotations.push(temp);
				  
				}
				}
				recog.base.set_state(745);
				recog.err_handler.sync(&mut recog.base)?;
				_la = recog.base.input.la(1);
			}
			recog.base.set_state(746);
			recog.base.match_token(DESTRUCTOR,&mut recog.err_handler)?;

			recog.base.set_state(748);
			recog.err_handler.sync(&mut recog.base)?;
			_la = recog.base.input.la(1);
			if _la==ASTERISK {
				{
				/*InvokeRule methodSpec*/
				recog.base.set_state(747);
				let tmp = recog.methodSpec()?;
				 cast_mut::<_,DestructorDeclContext >(&mut _localctx).method = Some(tmp.clone());
				  

				}
			}

			recog.base.set_state(751);
			recog.err_handler.sync(&mut recog.base)?;
			_la = recog.base.input.la(1);
			if ((((_la - 86)) & !0x3f) == 0 && ((1usize << (_la - 86)) & 519) != 0) {
				{
				/*InvokeRule ident*/
				recog.base.set_state(750);
				let tmp = recog.ident()?;
				 cast_mut::<_,DestructorDeclContext >(&mut _localctx).name = Some(tmp.clone());
				  

				}
			}

			recog.base.set_state(753);
			recog.base.match_token(L_PAREN,&mut recog.err_handler)?;

			recog.base.set_state(758);
			recog.err_handler.sync(&mut recog.base)?;
			_la = recog.base.input.la(1);
			if ((((_la - 86)) & !0x3f) == 0 && ((1usize << (_la - 86)) & 647) != 0) {
				{
				/*InvokeRule functionParamList*/
				recog.base.set_state(754);
				let tmp = recog.functionParamList()?;
				 cast_mut::<_,DestructorDeclContext >(&mut _localctx).params = Some(tmp.clone());
				  

				recog.base.set_state(756);
				recog.err_handler.sync(&mut recog.base)?;
				_la = recog.base.input.la(1);
				if _la==COMMA {
					{
					recog.base.set_state(755);
					recog.base.match_token(COMMA,&mut recog.err_handler)?;

					}
				}

				}
			}

			recog.base.set_state(760);
			recog.base.match_token(R_PAREN,&mut recog.err_handler)?;

			recog.base.set_state(763);
			recog.err_handler.sync(&mut recog.base)?;
			_la = recog.base.input.la(1);
			if _la==COLON {
				{
				recog.base.set_state(761);
				recog.base.match_token(COLON,&mut recog.err_handler)?;

				/*InvokeRule typeExpr*/
				recog.base.set_state(762);
				let tmp = recog.typeExpr_rec(0)?;
				 cast_mut::<_,DestructorDeclContext >(&mut _localctx).retType = Some(tmp.clone());
				  

				}
			}

			/*InvokeRule functionDef*/
			recog.base.set_state(765);
			let tmp = recog.functionDef()?;
			 cast_mut::<_,DestructorDeclContext >(&mut _localctx).def = Some(tmp.clone());
			  

			}
			Ok(())
		})();
		match result {
		Ok(_)=>{},
        Err(e @ ANTLRError::FallThrough(_)) => return Err(e),
		Err(ref re) => {
				//_localctx.exception = re;
				recog.err_handler.report_error(&mut recog.base, re);
				recog.err_handler.recover(&mut recog.base, re)?;
			}
		}
		recog.base.exit_rule();

		Ok(_localctx)
	}
}
//------------------- procDecl ----------------
pub type ProcDeclContextAll<'input> = ProcDeclContext<'input>;


pub type ProcDeclContext<'input> = BaseParserRuleContext<'input,ProcDeclContextExt<'input>>;

#[derive(Clone)]
pub struct ProcDeclContextExt<'input>{
	pub annotation: Option<Rc<AnnotationContextAll<'input>>>,
	pub annotations:Vec<Rc<AnnotationContextAll<'input>>>,
	pub procModifier: Option<Rc<ProcModifierContextAll<'input>>>,
	pub modifiers:Vec<Rc<ProcModifierContextAll<'input>>>,
	pub method: Option<Rc<MethodSpecContextAll<'input>>>,
	pub name: Option<Rc<IdentContextAll<'input>>>,
	pub typeParams: Option<Rc<GenericsContextAll<'input>>>,
	pub params: Option<Rc<FunctionParamListContextAll<'input>>>,
	pub retType: Option<Rc<TypeExprContextAll<'input>>>,
	pub typeConstraints: Option<Rc<WhereClauseContextAll<'input>>>,
	pub def: Option<Rc<FunctionDefContextAll<'input>>>,
ph:PhantomData<&'input str>
}

impl<'input> LibSLParserContext<'input> for ProcDeclContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for ProcDeclContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_procDecl(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_procDecl(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for ProcDeclContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_procDecl }
	//fn type_rule_index() -> usize where Self: Sized { RULE_procDecl }
}
antlr_rust::tid!{ProcDeclContextExt<'a>}

impl<'input> ProcDeclContextExt<'input>{
	fn new(parent: Option<Rc<dyn LibSLParserContext<'input> + 'input > >, invoking_state: isize) -> Rc<ProcDeclContextAll<'input>> {
		Rc::new(
			BaseParserRuleContext::new_parser_ctx(parent, invoking_state,ProcDeclContextExt{
				annotation: None, procModifier: None, method: None, name: None, typeParams: None, params: None, retType: None, typeConstraints: None, def: None, 
				annotations: Vec::new(), modifiers: Vec::new(), 
				ph:PhantomData
			}),
		)
	}
}

pub trait ProcDeclContextAttrs<'input>: LibSLParserContext<'input> + BorrowMut<ProcDeclContextExt<'input>>{

/// Retrieves first TerminalNode corresponding to token PROC
/// Returns `None` if there is no child corresponding to token PROC
fn PROC(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(PROC, 0)
}
/// Retrieves first TerminalNode corresponding to token L_PAREN
/// Returns `None` if there is no child corresponding to token L_PAREN
fn L_PAREN(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(L_PAREN, 0)
}
/// Retrieves first TerminalNode corresponding to token R_PAREN
/// Returns `None` if there is no child corresponding to token R_PAREN
fn R_PAREN(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(R_PAREN, 0)
}
fn ident(&self) -> Option<Rc<IdentContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}
fn functionDef(&self) -> Option<Rc<FunctionDefContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}
/// Retrieves first TerminalNode corresponding to token COLON
/// Returns `None` if there is no child corresponding to token COLON
fn COLON(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(COLON, 0)
}
fn annotation_all(&self) ->  Vec<Rc<AnnotationContextAll<'input>>> where Self:Sized{
	self.children_of_type()
}
fn annotation(&self, i: usize) -> Option<Rc<AnnotationContextAll<'input>>> where Self:Sized{
	self.child_of_type(i)
}
fn procModifier_all(&self) ->  Vec<Rc<ProcModifierContextAll<'input>>> where Self:Sized{
	self.children_of_type()
}
fn procModifier(&self, i: usize) -> Option<Rc<ProcModifierContextAll<'input>>> where Self:Sized{
	self.child_of_type(i)
}
fn methodSpec(&self) -> Option<Rc<MethodSpecContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}
fn generics(&self) -> Option<Rc<GenericsContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}
fn functionParamList(&self) -> Option<Rc<FunctionParamListContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}
fn typeExpr(&self) -> Option<Rc<TypeExprContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}
fn whereClause(&self) -> Option<Rc<WhereClauseContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}
/// Retrieves first TerminalNode corresponding to token COMMA
/// Returns `None` if there is no child corresponding to token COMMA
fn COMMA(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(COMMA, 0)
}

}

impl<'input> ProcDeclContextAttrs<'input> for ProcDeclContext<'input>{}

impl<'input, I, H> LibSLParser<'input, I, H>
where
    I: TokenStream<'input, TF = LocalTokenFactory<'input> > + TidAble<'input>,
    H: ErrorStrategy<'input,BaseParserType<'input,I>>
{
	pub fn procDecl(&mut self,)
	-> Result<Rc<ProcDeclContextAll<'input>>,ANTLRError> {
		let mut recog = self;
		let _parentctx = recog.ctx.take();
		let mut _localctx = ProcDeclContextExt::new(_parentctx.clone(), recog.base.get_state());
        recog.base.enter_rule(_localctx.clone(), 92, RULE_procDecl);
        let mut _localctx: Rc<ProcDeclContextAll> = _localctx;
		let mut _la: isize = -1;
		let result: Result<(), ANTLRError> = (|| {

			//recog.base.enter_outer_alt(_localctx.clone(), 1);
			recog.base.enter_outer_alt(None, 1);
			{
			recog.base.set_state(770);
			recog.err_handler.sync(&mut recog.base)?;
			_la = recog.base.input.la(1);
			while _la==AT {
				{
				{
				/*InvokeRule annotation*/
				recog.base.set_state(767);
				let tmp = recog.annotation()?;
				 cast_mut::<_,ProcDeclContext >(&mut _localctx).annotation = Some(tmp.clone());
				  

				let temp =  cast_mut::<_,ProcDeclContext >(&mut _localctx).annotation.clone().unwrap()
				 ;
				 cast_mut::<_,ProcDeclContext >(&mut _localctx).annotations.push(temp);
				  
				}
				}
				recog.base.set_state(772);
				recog.err_handler.sync(&mut recog.base)?;
				_la = recog.base.input.la(1);
			}
			recog.base.set_state(776);
			recog.err_handler.sync(&mut recog.base)?;
			_la = recog.base.input.la(1);
			while _la==PURE {
				{
				{
				/*InvokeRule procModifier*/
				recog.base.set_state(773);
				let tmp = recog.procModifier()?;
				 cast_mut::<_,ProcDeclContext >(&mut _localctx).procModifier = Some(tmp.clone());
				  

				let temp =  cast_mut::<_,ProcDeclContext >(&mut _localctx).procModifier.clone().unwrap()
				 ;
				 cast_mut::<_,ProcDeclContext >(&mut _localctx).modifiers.push(temp);
				  
				}
				}
				recog.base.set_state(778);
				recog.err_handler.sync(&mut recog.base)?;
				_la = recog.base.input.la(1);
			}
			recog.base.set_state(779);
			recog.base.match_token(PROC,&mut recog.err_handler)?;

			recog.base.set_state(781);
			recog.err_handler.sync(&mut recog.base)?;
			_la = recog.base.input.la(1);
			if _la==ASTERISK {
				{
				/*InvokeRule methodSpec*/
				recog.base.set_state(780);
				let tmp = recog.methodSpec()?;
				 cast_mut::<_,ProcDeclContext >(&mut _localctx).method = Some(tmp.clone());
				  

				}
			}

			/*InvokeRule ident*/
			recog.base.set_state(783);
			let tmp = recog.ident()?;
			 cast_mut::<_,ProcDeclContext >(&mut _localctx).name = Some(tmp.clone());
			  

			recog.base.set_state(785);
			recog.err_handler.sync(&mut recog.base)?;
			_la = recog.base.input.la(1);
			if _la==L_ANGLE {
				{
				/*InvokeRule generics*/
				recog.base.set_state(784);
				let tmp = recog.generics()?;
				 cast_mut::<_,ProcDeclContext >(&mut _localctx).typeParams = Some(tmp.clone());
				  

				}
			}

			recog.base.set_state(787);
			recog.base.match_token(L_PAREN,&mut recog.err_handler)?;

			recog.base.set_state(792);
			recog.err_handler.sync(&mut recog.base)?;
			_la = recog.base.input.la(1);
			if ((((_la - 86)) & !0x3f) == 0 && ((1usize << (_la - 86)) & 647) != 0) {
				{
				/*InvokeRule functionParamList*/
				recog.base.set_state(788);
				let tmp = recog.functionParamList()?;
				 cast_mut::<_,ProcDeclContext >(&mut _localctx).params = Some(tmp.clone());
				  

				recog.base.set_state(790);
				recog.err_handler.sync(&mut recog.base)?;
				_la = recog.base.input.la(1);
				if _la==COMMA {
					{
					recog.base.set_state(789);
					recog.base.match_token(COMMA,&mut recog.err_handler)?;

					}
				}

				}
			}

			recog.base.set_state(794);
			recog.base.match_token(R_PAREN,&mut recog.err_handler)?;

			recog.base.set_state(797);
			recog.err_handler.sync(&mut recog.base)?;
			_la = recog.base.input.la(1);
			if _la==COLON {
				{
				recog.base.set_state(795);
				recog.base.match_token(COLON,&mut recog.err_handler)?;

				/*InvokeRule typeExpr*/
				recog.base.set_state(796);
				let tmp = recog.typeExpr_rec(0)?;
				 cast_mut::<_,ProcDeclContext >(&mut _localctx).retType = Some(tmp.clone());
				  

				}
			}

			recog.base.set_state(800);
			recog.err_handler.sync(&mut recog.base)?;
			_la = recog.base.input.la(1);
			if _la==WHERE {
				{
				/*InvokeRule whereClause*/
				recog.base.set_state(799);
				let tmp = recog.whereClause()?;
				 cast_mut::<_,ProcDeclContext >(&mut _localctx).typeConstraints = Some(tmp.clone());
				  

				}
			}

			/*InvokeRule functionDef*/
			recog.base.set_state(802);
			let tmp = recog.functionDef()?;
			 cast_mut::<_,ProcDeclContext >(&mut _localctx).def = Some(tmp.clone());
			  

			}
			Ok(())
		})();
		match result {
		Ok(_)=>{},
        Err(e @ ANTLRError::FallThrough(_)) => return Err(e),
		Err(ref re) => {
				//_localctx.exception = re;
				recog.err_handler.report_error(&mut recog.base, re);
				recog.err_handler.recover(&mut recog.base, re)?;
			}
		}
		recog.base.exit_rule();

		Ok(_localctx)
	}
}
//------------------- procModifier ----------------
#[derive(Debug)]
pub enum ProcModifierContextAll<'input>{
	ProcModifierPureContext(ProcModifierPureContext<'input>),
Error(ProcModifierContext<'input>)
}
antlr_rust::tid!{ProcModifierContextAll<'a>}

impl<'input> antlr_rust::parser_rule_context::DerefSeal for ProcModifierContextAll<'input>{}

impl<'input> LibSLParserContext<'input> for ProcModifierContextAll<'input>{}

impl<'input> Deref for ProcModifierContextAll<'input>{
	type Target = dyn ProcModifierContextAttrs<'input> + 'input;
	fn deref(&self) -> &Self::Target{
		use ProcModifierContextAll::*;
		match self{
			ProcModifierPureContext(inner) => inner,
Error(inner) => inner
		}
	}
}
impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for ProcModifierContextAll<'input>{
    fn enter(&self, listener: &mut (dyn LibSLParserListener<'input> + 'a)) { self.deref().enter(listener) }
    fn exit(&self, listener: &mut (dyn LibSLParserListener<'input> + 'a)) { self.deref().exit(listener) }
}



pub type ProcModifierContext<'input> = BaseParserRuleContext<'input,ProcModifierContextExt<'input>>;

#[derive(Clone)]
pub struct ProcModifierContextExt<'input>{
ph:PhantomData<&'input str>
}

impl<'input> LibSLParserContext<'input> for ProcModifierContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for ProcModifierContext<'input>{
}

impl<'input> CustomRuleContext<'input> for ProcModifierContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_procModifier }
	//fn type_rule_index() -> usize where Self: Sized { RULE_procModifier }
}
antlr_rust::tid!{ProcModifierContextExt<'a>}

impl<'input> ProcModifierContextExt<'input>{
	fn new(parent: Option<Rc<dyn LibSLParserContext<'input> + 'input > >, invoking_state: isize) -> Rc<ProcModifierContextAll<'input>> {
		Rc::new(
		ProcModifierContextAll::Error(
			BaseParserRuleContext::new_parser_ctx(parent, invoking_state,ProcModifierContextExt{
				ph:PhantomData
			}),
		)
		)
	}
}

pub trait ProcModifierContextAttrs<'input>: LibSLParserContext<'input> + BorrowMut<ProcModifierContextExt<'input>>{


}

impl<'input> ProcModifierContextAttrs<'input> for ProcModifierContext<'input>{}

pub type ProcModifierPureContext<'input> = BaseParserRuleContext<'input,ProcModifierPureContextExt<'input>>;

pub trait ProcModifierPureContextAttrs<'input>: LibSLParserContext<'input>{
	/// Retrieves first TerminalNode corresponding to token PURE
	/// Returns `None` if there is no child corresponding to token PURE
	fn PURE(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(PURE, 0)
	}
}

impl<'input> ProcModifierPureContextAttrs<'input> for ProcModifierPureContext<'input>{}

pub struct ProcModifierPureContextExt<'input>{
	__base:ProcModifierContextExt<'input>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{ProcModifierPureContextExt<'a>}

impl<'input> LibSLParserContext<'input> for ProcModifierPureContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for ProcModifierPureContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_ProcModifierPure(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_ProcModifierPure(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for ProcModifierPureContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_procModifier }
	//fn type_rule_index() -> usize where Self: Sized { RULE_procModifier }
}

impl<'input> Borrow<ProcModifierContextExt<'input>> for ProcModifierPureContext<'input>{
	fn borrow(&self) -> &ProcModifierContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<ProcModifierContextExt<'input>> for ProcModifierPureContext<'input>{
	fn borrow_mut(&mut self) -> &mut ProcModifierContextExt<'input> { &mut self.__base }
}

impl<'input> ProcModifierContextAttrs<'input> for ProcModifierPureContext<'input> {}

impl<'input> ProcModifierPureContextExt<'input>{
	fn new(ctx: &dyn ProcModifierContextAttrs<'input>) -> Rc<ProcModifierContextAll<'input>>  {
		Rc::new(
			ProcModifierContextAll::ProcModifierPureContext(
				BaseParserRuleContext::copy_from(ctx,ProcModifierPureContextExt{
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

impl<'input, I, H> LibSLParser<'input, I, H>
where
    I: TokenStream<'input, TF = LocalTokenFactory<'input> > + TidAble<'input>,
    H: ErrorStrategy<'input,BaseParserType<'input,I>>
{
	pub fn procModifier(&mut self,)
	-> Result<Rc<ProcModifierContextAll<'input>>,ANTLRError> {
		let mut recog = self;
		let _parentctx = recog.ctx.take();
		let mut _localctx = ProcModifierContextExt::new(_parentctx.clone(), recog.base.get_state());
        recog.base.enter_rule(_localctx.clone(), 94, RULE_procModifier);
        let mut _localctx: Rc<ProcModifierContextAll> = _localctx;
		let result: Result<(), ANTLRError> = (|| {

			let tmp = ProcModifierPureContextExt::new(&**_localctx);
			recog.base.enter_outer_alt(Some(tmp.clone()), 1);
			_localctx = tmp;
			{
			recog.base.set_state(804);
			recog.base.match_token(PURE,&mut recog.err_handler)?;

			}
			Ok(())
		})();
		match result {
		Ok(_)=>{},
        Err(e @ ANTLRError::FallThrough(_)) => return Err(e),
		Err(ref re) => {
				//_localctx.exception = re;
				recog.err_handler.report_error(&mut recog.base, re);
				recog.err_handler.recover(&mut recog.base, re)?;
			}
		}
		recog.base.exit_rule();

		Ok(_localctx)
	}
}
//------------------- functionParamList ----------------
pub type FunctionParamListContextAll<'input> = FunctionParamListContext<'input>;


pub type FunctionParamListContext<'input> = BaseParserRuleContext<'input,FunctionParamListContextExt<'input>>;

#[derive(Clone)]
pub struct FunctionParamListContextExt<'input>{
	pub functionParam: Option<Rc<FunctionParamContextAll<'input>>>,
	pub params:Vec<Rc<FunctionParamContextAll<'input>>>,
ph:PhantomData<&'input str>
}

impl<'input> LibSLParserContext<'input> for FunctionParamListContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for FunctionParamListContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_functionParamList(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_functionParamList(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for FunctionParamListContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_functionParamList }
	//fn type_rule_index() -> usize where Self: Sized { RULE_functionParamList }
}
antlr_rust::tid!{FunctionParamListContextExt<'a>}

impl<'input> FunctionParamListContextExt<'input>{
	fn new(parent: Option<Rc<dyn LibSLParserContext<'input> + 'input > >, invoking_state: isize) -> Rc<FunctionParamListContextAll<'input>> {
		Rc::new(
			BaseParserRuleContext::new_parser_ctx(parent, invoking_state,FunctionParamListContextExt{
				functionParam: None, 
				params: Vec::new(), 
				ph:PhantomData
			}),
		)
	}
}

pub trait FunctionParamListContextAttrs<'input>: LibSLParserContext<'input> + BorrowMut<FunctionParamListContextExt<'input>>{

fn functionParam_all(&self) ->  Vec<Rc<FunctionParamContextAll<'input>>> where Self:Sized{
	self.children_of_type()
}
fn functionParam(&self, i: usize) -> Option<Rc<FunctionParamContextAll<'input>>> where Self:Sized{
	self.child_of_type(i)
}
/// Retrieves all `TerminalNode`s corresponding to token COMMA in current rule
fn COMMA_all(&self) -> Vec<Rc<TerminalNode<'input,LibSLParserContextType>>>  where Self:Sized{
	self.get_tokens(COMMA)
}
/// Retrieves 'i's TerminalNode corresponding to token COMMA, starting from 0.
/// Returns `None` if number of children corresponding to token COMMA is less or equal than `i`.
fn COMMA(&self, i: usize) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(COMMA, i)
}

}

impl<'input> FunctionParamListContextAttrs<'input> for FunctionParamListContext<'input>{}

impl<'input, I, H> LibSLParser<'input, I, H>
where
    I: TokenStream<'input, TF = LocalTokenFactory<'input> > + TidAble<'input>,
    H: ErrorStrategy<'input,BaseParserType<'input,I>>
{
	pub fn functionParamList(&mut self,)
	-> Result<Rc<FunctionParamListContextAll<'input>>,ANTLRError> {
		let mut recog = self;
		let _parentctx = recog.ctx.take();
		let mut _localctx = FunctionParamListContextExt::new(_parentctx.clone(), recog.base.get_state());
        recog.base.enter_rule(_localctx.clone(), 96, RULE_functionParamList);
        let mut _localctx: Rc<FunctionParamListContextAll> = _localctx;
		let result: Result<(), ANTLRError> = (|| {

			let mut _alt: isize;
			//recog.base.enter_outer_alt(_localctx.clone(), 1);
			recog.base.enter_outer_alt(None, 1);
			{
			/*InvokeRule functionParam*/
			recog.base.set_state(806);
			let tmp = recog.functionParam()?;
			 cast_mut::<_,FunctionParamListContext >(&mut _localctx).functionParam = Some(tmp.clone());
			  

			let temp =  cast_mut::<_,FunctionParamListContext >(&mut _localctx).functionParam.clone().unwrap()
			 ;
			 cast_mut::<_,FunctionParamListContext >(&mut _localctx).params.push(temp);
			  
			recog.base.set_state(811);
			recog.err_handler.sync(&mut recog.base)?;
			_alt = recog.interpreter.adaptive_predict(103,&mut recog.base)?;
			while { _alt!=2 && _alt!=INVALID_ALT } {
				if _alt==1 {
					{
					{
					recog.base.set_state(807);
					recog.base.match_token(COMMA,&mut recog.err_handler)?;

					/*InvokeRule functionParam*/
					recog.base.set_state(808);
					let tmp = recog.functionParam()?;
					 cast_mut::<_,FunctionParamListContext >(&mut _localctx).functionParam = Some(tmp.clone());
					  

					let temp =  cast_mut::<_,FunctionParamListContext >(&mut _localctx).functionParam.clone().unwrap()
					 ;
					 cast_mut::<_,FunctionParamListContext >(&mut _localctx).params.push(temp);
					  
					}
					} 
				}
				recog.base.set_state(813);
				recog.err_handler.sync(&mut recog.base)?;
				_alt = recog.interpreter.adaptive_predict(103,&mut recog.base)?;
			}
			}
			Ok(())
		})();
		match result {
		Ok(_)=>{},
        Err(e @ ANTLRError::FallThrough(_)) => return Err(e),
		Err(ref re) => {
				//_localctx.exception = re;
				recog.err_handler.report_error(&mut recog.base, re);
				recog.err_handler.recover(&mut recog.base, re)?;
			}
		}
		recog.base.exit_rule();

		Ok(_localctx)
	}
}
//------------------- functionParam ----------------
pub type FunctionParamContextAll<'input> = FunctionParamContext<'input>;


pub type FunctionParamContext<'input> = BaseParserRuleContext<'input,FunctionParamContextExt<'input>>;

#[derive(Clone)]
pub struct FunctionParamContextExt<'input>{
	pub annotation: Option<Rc<AnnotationContextAll<'input>>>,
	pub annotations:Vec<Rc<AnnotationContextAll<'input>>>,
	pub name: Option<Rc<IdentContextAll<'input>>>,
	pub r#type: Option<Rc<TypeExprContextAll<'input>>>,
ph:PhantomData<&'input str>
}

impl<'input> LibSLParserContext<'input> for FunctionParamContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for FunctionParamContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_functionParam(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_functionParam(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for FunctionParamContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_functionParam }
	//fn type_rule_index() -> usize where Self: Sized { RULE_functionParam }
}
antlr_rust::tid!{FunctionParamContextExt<'a>}

impl<'input> FunctionParamContextExt<'input>{
	fn new(parent: Option<Rc<dyn LibSLParserContext<'input> + 'input > >, invoking_state: isize) -> Rc<FunctionParamContextAll<'input>> {
		Rc::new(
			BaseParserRuleContext::new_parser_ctx(parent, invoking_state,FunctionParamContextExt{
				annotation: None, name: None, r#type: None, 
				annotations: Vec::new(), 
				ph:PhantomData
			}),
		)
	}
}

pub trait FunctionParamContextAttrs<'input>: LibSLParserContext<'input> + BorrowMut<FunctionParamContextExt<'input>>{

/// Retrieves first TerminalNode corresponding to token COLON
/// Returns `None` if there is no child corresponding to token COLON
fn COLON(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(COLON, 0)
}
fn ident(&self) -> Option<Rc<IdentContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}
fn typeExpr(&self) -> Option<Rc<TypeExprContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}
fn annotation_all(&self) ->  Vec<Rc<AnnotationContextAll<'input>>> where Self:Sized{
	self.children_of_type()
}
fn annotation(&self, i: usize) -> Option<Rc<AnnotationContextAll<'input>>> where Self:Sized{
	self.child_of_type(i)
}

}

impl<'input> FunctionParamContextAttrs<'input> for FunctionParamContext<'input>{}

impl<'input, I, H> LibSLParser<'input, I, H>
where
    I: TokenStream<'input, TF = LocalTokenFactory<'input> > + TidAble<'input>,
    H: ErrorStrategy<'input,BaseParserType<'input,I>>
{
	pub fn functionParam(&mut self,)
	-> Result<Rc<FunctionParamContextAll<'input>>,ANTLRError> {
		let mut recog = self;
		let _parentctx = recog.ctx.take();
		let mut _localctx = FunctionParamContextExt::new(_parentctx.clone(), recog.base.get_state());
        recog.base.enter_rule(_localctx.clone(), 98, RULE_functionParam);
        let mut _localctx: Rc<FunctionParamContextAll> = _localctx;
		let mut _la: isize = -1;
		let result: Result<(), ANTLRError> = (|| {

			//recog.base.enter_outer_alt(_localctx.clone(), 1);
			recog.base.enter_outer_alt(None, 1);
			{
			recog.base.set_state(817);
			recog.err_handler.sync(&mut recog.base)?;
			_la = recog.base.input.la(1);
			while _la==AT {
				{
				{
				/*InvokeRule annotation*/
				recog.base.set_state(814);
				let tmp = recog.annotation()?;
				 cast_mut::<_,FunctionParamContext >(&mut _localctx).annotation = Some(tmp.clone());
				  

				let temp =  cast_mut::<_,FunctionParamContext >(&mut _localctx).annotation.clone().unwrap()
				 ;
				 cast_mut::<_,FunctionParamContext >(&mut _localctx).annotations.push(temp);
				  
				}
				}
				recog.base.set_state(819);
				recog.err_handler.sync(&mut recog.base)?;
				_la = recog.base.input.la(1);
			}
			/*InvokeRule ident*/
			recog.base.set_state(820);
			let tmp = recog.ident()?;
			 cast_mut::<_,FunctionParamContext >(&mut _localctx).name = Some(tmp.clone());
			  

			recog.base.set_state(821);
			recog.base.match_token(COLON,&mut recog.err_handler)?;

			/*InvokeRule typeExpr*/
			recog.base.set_state(822);
			let tmp = recog.typeExpr_rec(0)?;
			 cast_mut::<_,FunctionParamContext >(&mut _localctx).r#type = Some(tmp.clone());
			  

			}
			Ok(())
		})();
		match result {
		Ok(_)=>{},
        Err(e @ ANTLRError::FallThrough(_)) => return Err(e),
		Err(ref re) => {
				//_localctx.exception = re;
				recog.err_handler.report_error(&mut recog.base, re);
				recog.err_handler.recover(&mut recog.base, re)?;
			}
		}
		recog.base.exit_rule();

		Ok(_localctx)
	}
}
//------------------- functionBody ----------------
pub type FunctionBodyContextAll<'input> = FunctionBodyContext<'input>;


pub type FunctionBodyContext<'input> = BaseParserRuleContext<'input,FunctionBodyContextExt<'input>>;

#[derive(Clone)]
pub struct FunctionBodyContextExt<'input>{
	pub contract: Option<Rc<ContractContextAll<'input>>>,
	pub contracts:Vec<Rc<ContractContextAll<'input>>>,
	pub stmt: Option<Rc<StmtContextAll<'input>>>,
	pub stmts:Vec<Rc<StmtContextAll<'input>>>,
ph:PhantomData<&'input str>
}

impl<'input> LibSLParserContext<'input> for FunctionBodyContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for FunctionBodyContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_functionBody(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_functionBody(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for FunctionBodyContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_functionBody }
	//fn type_rule_index() -> usize where Self: Sized { RULE_functionBody }
}
antlr_rust::tid!{FunctionBodyContextExt<'a>}

impl<'input> FunctionBodyContextExt<'input>{
	fn new(parent: Option<Rc<dyn LibSLParserContext<'input> + 'input > >, invoking_state: isize) -> Rc<FunctionBodyContextAll<'input>> {
		Rc::new(
			BaseParserRuleContext::new_parser_ctx(parent, invoking_state,FunctionBodyContextExt{
				contract: None, stmt: None, 
				contracts: Vec::new(), stmts: Vec::new(), 
				ph:PhantomData
			}),
		)
	}
}

pub trait FunctionBodyContextAttrs<'input>: LibSLParserContext<'input> + BorrowMut<FunctionBodyContextExt<'input>>{

fn contract_all(&self) ->  Vec<Rc<ContractContextAll<'input>>> where Self:Sized{
	self.children_of_type()
}
fn contract(&self, i: usize) -> Option<Rc<ContractContextAll<'input>>> where Self:Sized{
	self.child_of_type(i)
}
fn stmt_all(&self) ->  Vec<Rc<StmtContextAll<'input>>> where Self:Sized{
	self.children_of_type()
}
fn stmt(&self, i: usize) -> Option<Rc<StmtContextAll<'input>>> where Self:Sized{
	self.child_of_type(i)
}

}

impl<'input> FunctionBodyContextAttrs<'input> for FunctionBodyContext<'input>{}

impl<'input, I, H> LibSLParser<'input, I, H>
where
    I: TokenStream<'input, TF = LocalTokenFactory<'input> > + TidAble<'input>,
    H: ErrorStrategy<'input,BaseParserType<'input,I>>
{
	pub fn functionBody(&mut self,)
	-> Result<Rc<FunctionBodyContextAll<'input>>,ANTLRError> {
		let mut recog = self;
		let _parentctx = recog.ctx.take();
		let mut _localctx = FunctionBodyContextExt::new(_parentctx.clone(), recog.base.get_state());
        recog.base.enter_rule(_localctx.clone(), 100, RULE_functionBody);
        let mut _localctx: Rc<FunctionBodyContextAll> = _localctx;
		let mut _la: isize = -1;
		let result: Result<(), ANTLRError> = (|| {

			//recog.base.enter_outer_alt(_localctx.clone(), 1);
			recog.base.enter_outer_alt(None, 1);
			{
			recog.base.set_state(827);
			recog.err_handler.sync(&mut recog.base)?;
			_la = recog.base.input.la(1);
			while ((((_la - 70)) & !0x3f) == 0 && ((1usize << (_la - 70)) & 7) != 0) {
				{
				{
				/*InvokeRule contract*/
				recog.base.set_state(824);
				let tmp = recog.contract()?;
				 cast_mut::<_,FunctionBodyContext >(&mut _localctx).contract = Some(tmp.clone());
				  

				let temp =  cast_mut::<_,FunctionBodyContext >(&mut _localctx).contract.clone().unwrap()
				 ;
				 cast_mut::<_,FunctionBodyContext >(&mut _localctx).contracts.push(temp);
				  
				}
				}
				recog.base.set_state(829);
				recog.err_handler.sync(&mut recog.base)?;
				_la = recog.base.input.la(1);
			}
			recog.base.set_state(833);
			recog.err_handler.sync(&mut recog.base)?;
			_la = recog.base.input.la(1);
			while (((_la) & !0x3f) == 0 && ((1usize << _la) & 68682064) != 0) || ((((_la - 35)) & !0x3f) == 0 && ((1usize << (_la - 35)) & 281018369) != 0) || ((((_la - 69)) & !0x3f) == 0 && ((1usize << (_la - 69)) & 533598385) != 0) {
				{
				{
				/*InvokeRule stmt*/
				recog.base.set_state(830);
				let tmp = recog.stmt()?;
				 cast_mut::<_,FunctionBodyContext >(&mut _localctx).stmt = Some(tmp.clone());
				  

				let temp =  cast_mut::<_,FunctionBodyContext >(&mut _localctx).stmt.clone().unwrap()
				 ;
				 cast_mut::<_,FunctionBodyContext >(&mut _localctx).stmts.push(temp);
				  
				}
				}
				recog.base.set_state(835);
				recog.err_handler.sync(&mut recog.base)?;
				_la = recog.base.input.la(1);
			}
			}
			Ok(())
		})();
		match result {
		Ok(_)=>{},
        Err(e @ ANTLRError::FallThrough(_)) => return Err(e),
		Err(ref re) => {
				//_localctx.exception = re;
				recog.err_handler.report_error(&mut recog.base, re);
				recog.err_handler.recover(&mut recog.base, re)?;
			}
		}
		recog.base.exit_rule();

		Ok(_localctx)
	}
}
//------------------- contract ----------------
#[derive(Debug)]
pub enum ContractContextAll<'input>{
	ContractRequiresContext(ContractRequiresContext<'input>),
	ContractAssignsContext(ContractAssignsContext<'input>),
	ContractEnsuresContext(ContractEnsuresContext<'input>),
Error(ContractContext<'input>)
}
antlr_rust::tid!{ContractContextAll<'a>}

impl<'input> antlr_rust::parser_rule_context::DerefSeal for ContractContextAll<'input>{}

impl<'input> LibSLParserContext<'input> for ContractContextAll<'input>{}

impl<'input> Deref for ContractContextAll<'input>{
	type Target = dyn ContractContextAttrs<'input> + 'input;
	fn deref(&self) -> &Self::Target{
		use ContractContextAll::*;
		match self{
			ContractRequiresContext(inner) => inner,
			ContractAssignsContext(inner) => inner,
			ContractEnsuresContext(inner) => inner,
Error(inner) => inner
		}
	}
}
impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for ContractContextAll<'input>{
    fn enter(&self, listener: &mut (dyn LibSLParserListener<'input> + 'a)) { self.deref().enter(listener) }
    fn exit(&self, listener: &mut (dyn LibSLParserListener<'input> + 'a)) { self.deref().exit(listener) }
}



pub type ContractContext<'input> = BaseParserRuleContext<'input,ContractContextExt<'input>>;

#[derive(Clone)]
pub struct ContractContextExt<'input>{
ph:PhantomData<&'input str>
}

impl<'input> LibSLParserContext<'input> for ContractContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for ContractContext<'input>{
}

impl<'input> CustomRuleContext<'input> for ContractContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_contract }
	//fn type_rule_index() -> usize where Self: Sized { RULE_contract }
}
antlr_rust::tid!{ContractContextExt<'a>}

impl<'input> ContractContextExt<'input>{
	fn new(parent: Option<Rc<dyn LibSLParserContext<'input> + 'input > >, invoking_state: isize) -> Rc<ContractContextAll<'input>> {
		Rc::new(
		ContractContextAll::Error(
			BaseParserRuleContext::new_parser_ctx(parent, invoking_state,ContractContextExt{
				ph:PhantomData
			}),
		)
		)
	}
}

pub trait ContractContextAttrs<'input>: LibSLParserContext<'input> + BorrowMut<ContractContextExt<'input>>{


}

impl<'input> ContractContextAttrs<'input> for ContractContext<'input>{}

pub type ContractRequiresContext<'input> = BaseParserRuleContext<'input,ContractRequiresContextExt<'input>>;

pub trait ContractRequiresContextAttrs<'input>: LibSLParserContext<'input>{
	fn requiresContract(&self) -> Option<Rc<RequiresContractContextAll<'input>>> where Self:Sized{
		self.child_of_type(0)
	}
}

impl<'input> ContractRequiresContextAttrs<'input> for ContractRequiresContext<'input>{}

pub struct ContractRequiresContextExt<'input>{
	__base:ContractContextExt<'input>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{ContractRequiresContextExt<'a>}

impl<'input> LibSLParserContext<'input> for ContractRequiresContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for ContractRequiresContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_ContractRequires(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_ContractRequires(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for ContractRequiresContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_contract }
	//fn type_rule_index() -> usize where Self: Sized { RULE_contract }
}

impl<'input> Borrow<ContractContextExt<'input>> for ContractRequiresContext<'input>{
	fn borrow(&self) -> &ContractContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<ContractContextExt<'input>> for ContractRequiresContext<'input>{
	fn borrow_mut(&mut self) -> &mut ContractContextExt<'input> { &mut self.__base }
}

impl<'input> ContractContextAttrs<'input> for ContractRequiresContext<'input> {}

impl<'input> ContractRequiresContextExt<'input>{
	fn new(ctx: &dyn ContractContextAttrs<'input>) -> Rc<ContractContextAll<'input>>  {
		Rc::new(
			ContractContextAll::ContractRequiresContext(
				BaseParserRuleContext::copy_from(ctx,ContractRequiresContextExt{
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type ContractAssignsContext<'input> = BaseParserRuleContext<'input,ContractAssignsContextExt<'input>>;

pub trait ContractAssignsContextAttrs<'input>: LibSLParserContext<'input>{
	fn assignsContract(&self) -> Option<Rc<AssignsContractContextAll<'input>>> where Self:Sized{
		self.child_of_type(0)
	}
}

impl<'input> ContractAssignsContextAttrs<'input> for ContractAssignsContext<'input>{}

pub struct ContractAssignsContextExt<'input>{
	__base:ContractContextExt<'input>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{ContractAssignsContextExt<'a>}

impl<'input> LibSLParserContext<'input> for ContractAssignsContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for ContractAssignsContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_ContractAssigns(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_ContractAssigns(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for ContractAssignsContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_contract }
	//fn type_rule_index() -> usize where Self: Sized { RULE_contract }
}

impl<'input> Borrow<ContractContextExt<'input>> for ContractAssignsContext<'input>{
	fn borrow(&self) -> &ContractContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<ContractContextExt<'input>> for ContractAssignsContext<'input>{
	fn borrow_mut(&mut self) -> &mut ContractContextExt<'input> { &mut self.__base }
}

impl<'input> ContractContextAttrs<'input> for ContractAssignsContext<'input> {}

impl<'input> ContractAssignsContextExt<'input>{
	fn new(ctx: &dyn ContractContextAttrs<'input>) -> Rc<ContractContextAll<'input>>  {
		Rc::new(
			ContractContextAll::ContractAssignsContext(
				BaseParserRuleContext::copy_from(ctx,ContractAssignsContextExt{
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type ContractEnsuresContext<'input> = BaseParserRuleContext<'input,ContractEnsuresContextExt<'input>>;

pub trait ContractEnsuresContextAttrs<'input>: LibSLParserContext<'input>{
	fn ensuresContract(&self) -> Option<Rc<EnsuresContractContextAll<'input>>> where Self:Sized{
		self.child_of_type(0)
	}
}

impl<'input> ContractEnsuresContextAttrs<'input> for ContractEnsuresContext<'input>{}

pub struct ContractEnsuresContextExt<'input>{
	__base:ContractContextExt<'input>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{ContractEnsuresContextExt<'a>}

impl<'input> LibSLParserContext<'input> for ContractEnsuresContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for ContractEnsuresContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_ContractEnsures(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_ContractEnsures(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for ContractEnsuresContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_contract }
	//fn type_rule_index() -> usize where Self: Sized { RULE_contract }
}

impl<'input> Borrow<ContractContextExt<'input>> for ContractEnsuresContext<'input>{
	fn borrow(&self) -> &ContractContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<ContractContextExt<'input>> for ContractEnsuresContext<'input>{
	fn borrow_mut(&mut self) -> &mut ContractContextExt<'input> { &mut self.__base }
}

impl<'input> ContractContextAttrs<'input> for ContractEnsuresContext<'input> {}

impl<'input> ContractEnsuresContextExt<'input>{
	fn new(ctx: &dyn ContractContextAttrs<'input>) -> Rc<ContractContextAll<'input>>  {
		Rc::new(
			ContractContextAll::ContractEnsuresContext(
				BaseParserRuleContext::copy_from(ctx,ContractEnsuresContextExt{
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

impl<'input, I, H> LibSLParser<'input, I, H>
where
    I: TokenStream<'input, TF = LocalTokenFactory<'input> > + TidAble<'input>,
    H: ErrorStrategy<'input,BaseParserType<'input,I>>
{
	pub fn contract(&mut self,)
	-> Result<Rc<ContractContextAll<'input>>,ANTLRError> {
		let mut recog = self;
		let _parentctx = recog.ctx.take();
		let mut _localctx = ContractContextExt::new(_parentctx.clone(), recog.base.get_state());
        recog.base.enter_rule(_localctx.clone(), 102, RULE_contract);
        let mut _localctx: Rc<ContractContextAll> = _localctx;
		let result: Result<(), ANTLRError> = (|| {

			recog.base.set_state(839);
			recog.err_handler.sync(&mut recog.base)?;
			match recog.base.input.la(1) {
			 REQUIRES 
				=> {
					let tmp = ContractRequiresContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 1);
					_localctx = tmp;
					{
					/*InvokeRule requiresContract*/
					recog.base.set_state(836);
					recog.requiresContract()?;

					}
				}

			 ENSURES 
				=> {
					let tmp = ContractEnsuresContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 2);
					_localctx = tmp;
					{
					/*InvokeRule ensuresContract*/
					recog.base.set_state(837);
					recog.ensuresContract()?;

					}
				}

			 ASSIGNS 
				=> {
					let tmp = ContractAssignsContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 3);
					_localctx = tmp;
					{
					/*InvokeRule assignsContract*/
					recog.base.set_state(838);
					recog.assignsContract()?;

					}
				}

				_ => Err(ANTLRError::NoAltError(NoViableAltError::new(&mut recog.base)))?
			}
			Ok(())
		})();
		match result {
		Ok(_)=>{},
        Err(e @ ANTLRError::FallThrough(_)) => return Err(e),
		Err(ref re) => {
				//_localctx.exception = re;
				recog.err_handler.report_error(&mut recog.base, re);
				recog.err_handler.recover(&mut recog.base, re)?;
			}
		}
		recog.base.exit_rule();

		Ok(_localctx)
	}
}
//------------------- requiresContract ----------------
pub type RequiresContractContextAll<'input> = RequiresContractContext<'input>;


pub type RequiresContractContext<'input> = BaseParserRuleContext<'input,RequiresContractContextExt<'input>>;

#[derive(Clone)]
pub struct RequiresContractContextExt<'input>{
	pub name: Option<Rc<IdentContextAll<'input>>>,
	pub spec: Option<Rc<ContractPredicateContextAll<'input>>>,
ph:PhantomData<&'input str>
}

impl<'input> LibSLParserContext<'input> for RequiresContractContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for RequiresContractContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_requiresContract(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_requiresContract(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for RequiresContractContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_requiresContract }
	//fn type_rule_index() -> usize where Self: Sized { RULE_requiresContract }
}
antlr_rust::tid!{RequiresContractContextExt<'a>}

impl<'input> RequiresContractContextExt<'input>{
	fn new(parent: Option<Rc<dyn LibSLParserContext<'input> + 'input > >, invoking_state: isize) -> Rc<RequiresContractContextAll<'input>> {
		Rc::new(
			BaseParserRuleContext::new_parser_ctx(parent, invoking_state,RequiresContractContextExt{
				name: None, spec: None, 
				ph:PhantomData
			}),
		)
	}
}

pub trait RequiresContractContextAttrs<'input>: LibSLParserContext<'input> + BorrowMut<RequiresContractContextExt<'input>>{

/// Retrieves first TerminalNode corresponding to token REQUIRES
/// Returns `None` if there is no child corresponding to token REQUIRES
fn REQUIRES(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(REQUIRES, 0)
}
fn contractPredicate(&self) -> Option<Rc<ContractPredicateContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}
/// Retrieves first TerminalNode corresponding to token COLON
/// Returns `None` if there is no child corresponding to token COLON
fn COLON(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(COLON, 0)
}
fn ident(&self) -> Option<Rc<IdentContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}

}

impl<'input> RequiresContractContextAttrs<'input> for RequiresContractContext<'input>{}

impl<'input, I, H> LibSLParser<'input, I, H>
where
    I: TokenStream<'input, TF = LocalTokenFactory<'input> > + TidAble<'input>,
    H: ErrorStrategy<'input,BaseParserType<'input,I>>
{
	pub fn requiresContract(&mut self,)
	-> Result<Rc<RequiresContractContextAll<'input>>,ANTLRError> {
		let mut recog = self;
		let _parentctx = recog.ctx.take();
		let mut _localctx = RequiresContractContextExt::new(_parentctx.clone(), recog.base.get_state());
        recog.base.enter_rule(_localctx.clone(), 104, RULE_requiresContract);
        let mut _localctx: Rc<RequiresContractContextAll> = _localctx;
		let result: Result<(), ANTLRError> = (|| {

			//recog.base.enter_outer_alt(_localctx.clone(), 1);
			recog.base.enter_outer_alt(None, 1);
			{
			recog.base.set_state(841);
			recog.base.match_token(REQUIRES,&mut recog.err_handler)?;

			recog.base.set_state(845);
			recog.err_handler.sync(&mut recog.base)?;
			match  recog.interpreter.adaptive_predict(108,&mut recog.base)? {
				x if x == 1=>{
					{
					/*InvokeRule ident*/
					recog.base.set_state(842);
					let tmp = recog.ident()?;
					 cast_mut::<_,RequiresContractContext >(&mut _localctx).name = Some(tmp.clone());
					  

					recog.base.set_state(843);
					recog.base.match_token(COLON,&mut recog.err_handler)?;

					}
				}

				_ => {}
			}
			/*InvokeRule contractPredicate*/
			recog.base.set_state(847);
			let tmp = recog.contractPredicate()?;
			 cast_mut::<_,RequiresContractContext >(&mut _localctx).spec = Some(tmp.clone());
			  

			}
			Ok(())
		})();
		match result {
		Ok(_)=>{},
        Err(e @ ANTLRError::FallThrough(_)) => return Err(e),
		Err(ref re) => {
				//_localctx.exception = re;
				recog.err_handler.report_error(&mut recog.base, re);
				recog.err_handler.recover(&mut recog.base, re)?;
			}
		}
		recog.base.exit_rule();

		Ok(_localctx)
	}
}
//------------------- ensuresContract ----------------
pub type EnsuresContractContextAll<'input> = EnsuresContractContext<'input>;


pub type EnsuresContractContext<'input> = BaseParserRuleContext<'input,EnsuresContractContextExt<'input>>;

#[derive(Clone)]
pub struct EnsuresContractContextExt<'input>{
	pub name: Option<Rc<IdentContextAll<'input>>>,
	pub spec: Option<Rc<ContractPredicateContextAll<'input>>>,
ph:PhantomData<&'input str>
}

impl<'input> LibSLParserContext<'input> for EnsuresContractContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for EnsuresContractContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_ensuresContract(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_ensuresContract(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for EnsuresContractContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_ensuresContract }
	//fn type_rule_index() -> usize where Self: Sized { RULE_ensuresContract }
}
antlr_rust::tid!{EnsuresContractContextExt<'a>}

impl<'input> EnsuresContractContextExt<'input>{
	fn new(parent: Option<Rc<dyn LibSLParserContext<'input> + 'input > >, invoking_state: isize) -> Rc<EnsuresContractContextAll<'input>> {
		Rc::new(
			BaseParserRuleContext::new_parser_ctx(parent, invoking_state,EnsuresContractContextExt{
				name: None, spec: None, 
				ph:PhantomData
			}),
		)
	}
}

pub trait EnsuresContractContextAttrs<'input>: LibSLParserContext<'input> + BorrowMut<EnsuresContractContextExt<'input>>{

/// Retrieves first TerminalNode corresponding to token ENSURES
/// Returns `None` if there is no child corresponding to token ENSURES
fn ENSURES(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(ENSURES, 0)
}
fn contractPredicate(&self) -> Option<Rc<ContractPredicateContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}
/// Retrieves first TerminalNode corresponding to token COLON
/// Returns `None` if there is no child corresponding to token COLON
fn COLON(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(COLON, 0)
}
fn ident(&self) -> Option<Rc<IdentContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}

}

impl<'input> EnsuresContractContextAttrs<'input> for EnsuresContractContext<'input>{}

impl<'input, I, H> LibSLParser<'input, I, H>
where
    I: TokenStream<'input, TF = LocalTokenFactory<'input> > + TidAble<'input>,
    H: ErrorStrategy<'input,BaseParserType<'input,I>>
{
	pub fn ensuresContract(&mut self,)
	-> Result<Rc<EnsuresContractContextAll<'input>>,ANTLRError> {
		let mut recog = self;
		let _parentctx = recog.ctx.take();
		let mut _localctx = EnsuresContractContextExt::new(_parentctx.clone(), recog.base.get_state());
        recog.base.enter_rule(_localctx.clone(), 106, RULE_ensuresContract);
        let mut _localctx: Rc<EnsuresContractContextAll> = _localctx;
		let result: Result<(), ANTLRError> = (|| {

			//recog.base.enter_outer_alt(_localctx.clone(), 1);
			recog.base.enter_outer_alt(None, 1);
			{
			recog.base.set_state(849);
			recog.base.match_token(ENSURES,&mut recog.err_handler)?;

			recog.base.set_state(853);
			recog.err_handler.sync(&mut recog.base)?;
			match  recog.interpreter.adaptive_predict(109,&mut recog.base)? {
				x if x == 1=>{
					{
					/*InvokeRule ident*/
					recog.base.set_state(850);
					let tmp = recog.ident()?;
					 cast_mut::<_,EnsuresContractContext >(&mut _localctx).name = Some(tmp.clone());
					  

					recog.base.set_state(851);
					recog.base.match_token(COLON,&mut recog.err_handler)?;

					}
				}

				_ => {}
			}
			/*InvokeRule contractPredicate*/
			recog.base.set_state(855);
			let tmp = recog.contractPredicate()?;
			 cast_mut::<_,EnsuresContractContext >(&mut _localctx).spec = Some(tmp.clone());
			  

			}
			Ok(())
		})();
		match result {
		Ok(_)=>{},
        Err(e @ ANTLRError::FallThrough(_)) => return Err(e),
		Err(ref re) => {
				//_localctx.exception = re;
				recog.err_handler.report_error(&mut recog.base, re);
				recog.err_handler.recover(&mut recog.base, re)?;
			}
		}
		recog.base.exit_rule();

		Ok(_localctx)
	}
}
//------------------- assignsContract ----------------
pub type AssignsContractContextAll<'input> = AssignsContractContext<'input>;


pub type AssignsContractContext<'input> = BaseParserRuleContext<'input,AssignsContractContextExt<'input>>;

#[derive(Clone)]
pub struct AssignsContractContextExt<'input>{
	pub name: Option<Rc<IdentContextAll<'input>>>,
	pub spec: Option<Rc<ExprContextAll<'input>>>,
ph:PhantomData<&'input str>
}

impl<'input> LibSLParserContext<'input> for AssignsContractContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for AssignsContractContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_assignsContract(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_assignsContract(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for AssignsContractContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_assignsContract }
	//fn type_rule_index() -> usize where Self: Sized { RULE_assignsContract }
}
antlr_rust::tid!{AssignsContractContextExt<'a>}

impl<'input> AssignsContractContextExt<'input>{
	fn new(parent: Option<Rc<dyn LibSLParserContext<'input> + 'input > >, invoking_state: isize) -> Rc<AssignsContractContextAll<'input>> {
		Rc::new(
			BaseParserRuleContext::new_parser_ctx(parent, invoking_state,AssignsContractContextExt{
				name: None, spec: None, 
				ph:PhantomData
			}),
		)
	}
}

pub trait AssignsContractContextAttrs<'input>: LibSLParserContext<'input> + BorrowMut<AssignsContractContextExt<'input>>{

/// Retrieves first TerminalNode corresponding to token ASSIGNS
/// Returns `None` if there is no child corresponding to token ASSIGNS
fn ASSIGNS(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(ASSIGNS, 0)
}
/// Retrieves first TerminalNode corresponding to token SEMICOLON
/// Returns `None` if there is no child corresponding to token SEMICOLON
fn SEMICOLON(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(SEMICOLON, 0)
}
fn expr(&self) -> Option<Rc<ExprContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}
/// Retrieves first TerminalNode corresponding to token COLON
/// Returns `None` if there is no child corresponding to token COLON
fn COLON(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(COLON, 0)
}
fn ident(&self) -> Option<Rc<IdentContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}

}

impl<'input> AssignsContractContextAttrs<'input> for AssignsContractContext<'input>{}

impl<'input, I, H> LibSLParser<'input, I, H>
where
    I: TokenStream<'input, TF = LocalTokenFactory<'input> > + TidAble<'input>,
    H: ErrorStrategy<'input,BaseParserType<'input,I>>
{
	pub fn assignsContract(&mut self,)
	-> Result<Rc<AssignsContractContextAll<'input>>,ANTLRError> {
		let mut recog = self;
		let _parentctx = recog.ctx.take();
		let mut _localctx = AssignsContractContextExt::new(_parentctx.clone(), recog.base.get_state());
        recog.base.enter_rule(_localctx.clone(), 108, RULE_assignsContract);
        let mut _localctx: Rc<AssignsContractContextAll> = _localctx;
		let result: Result<(), ANTLRError> = (|| {

			//recog.base.enter_outer_alt(_localctx.clone(), 1);
			recog.base.enter_outer_alt(None, 1);
			{
			recog.base.set_state(857);
			recog.base.match_token(ASSIGNS,&mut recog.err_handler)?;

			recog.base.set_state(861);
			recog.err_handler.sync(&mut recog.base)?;
			match  recog.interpreter.adaptive_predict(110,&mut recog.base)? {
				x if x == 1=>{
					{
					/*InvokeRule ident*/
					recog.base.set_state(858);
					let tmp = recog.ident()?;
					 cast_mut::<_,AssignsContractContext >(&mut _localctx).name = Some(tmp.clone());
					  

					recog.base.set_state(859);
					recog.base.match_token(COLON,&mut recog.err_handler)?;

					}
				}

				_ => {}
			}
			/*InvokeRule expr*/
			recog.base.set_state(863);
			let tmp = recog.expr_rec(0)?;
			 cast_mut::<_,AssignsContractContext >(&mut _localctx).spec = Some(tmp.clone());
			  

			recog.base.set_state(864);
			recog.base.match_token(SEMICOLON,&mut recog.err_handler)?;

			}
			Ok(())
		})();
		match result {
		Ok(_)=>{},
        Err(e @ ANTLRError::FallThrough(_)) => return Err(e),
		Err(ref re) => {
				//_localctx.exception = re;
				recog.err_handler.report_error(&mut recog.base, re);
				recog.err_handler.recover(&mut recog.base, re)?;
			}
		}
		recog.base.exit_rule();

		Ok(_localctx)
	}
}
//------------------- contractPredicate ----------------
#[derive(Debug)]
pub enum ContractPredicateContextAll<'input>{
	ContractPredicateIfContext(ContractPredicateIfContext<'input>),
	ContractPredicateBlockContext(ContractPredicateBlockContext<'input>),
	ContractPredicateExprContext(ContractPredicateExprContext<'input>),
Error(ContractPredicateContext<'input>)
}
antlr_rust::tid!{ContractPredicateContextAll<'a>}

impl<'input> antlr_rust::parser_rule_context::DerefSeal for ContractPredicateContextAll<'input>{}

impl<'input> LibSLParserContext<'input> for ContractPredicateContextAll<'input>{}

impl<'input> Deref for ContractPredicateContextAll<'input>{
	type Target = dyn ContractPredicateContextAttrs<'input> + 'input;
	fn deref(&self) -> &Self::Target{
		use ContractPredicateContextAll::*;
		match self{
			ContractPredicateIfContext(inner) => inner,
			ContractPredicateBlockContext(inner) => inner,
			ContractPredicateExprContext(inner) => inner,
Error(inner) => inner
		}
	}
}
impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for ContractPredicateContextAll<'input>{
    fn enter(&self, listener: &mut (dyn LibSLParserListener<'input> + 'a)) { self.deref().enter(listener) }
    fn exit(&self, listener: &mut (dyn LibSLParserListener<'input> + 'a)) { self.deref().exit(listener) }
}



pub type ContractPredicateContext<'input> = BaseParserRuleContext<'input,ContractPredicateContextExt<'input>>;

#[derive(Clone)]
pub struct ContractPredicateContextExt<'input>{
ph:PhantomData<&'input str>
}

impl<'input> LibSLParserContext<'input> for ContractPredicateContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for ContractPredicateContext<'input>{
}

impl<'input> CustomRuleContext<'input> for ContractPredicateContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_contractPredicate }
	//fn type_rule_index() -> usize where Self: Sized { RULE_contractPredicate }
}
antlr_rust::tid!{ContractPredicateContextExt<'a>}

impl<'input> ContractPredicateContextExt<'input>{
	fn new(parent: Option<Rc<dyn LibSLParserContext<'input> + 'input > >, invoking_state: isize) -> Rc<ContractPredicateContextAll<'input>> {
		Rc::new(
		ContractPredicateContextAll::Error(
			BaseParserRuleContext::new_parser_ctx(parent, invoking_state,ContractPredicateContextExt{
				ph:PhantomData
			}),
		)
		)
	}
}

pub trait ContractPredicateContextAttrs<'input>: LibSLParserContext<'input> + BorrowMut<ContractPredicateContextExt<'input>>{


}

impl<'input> ContractPredicateContextAttrs<'input> for ContractPredicateContext<'input>{}

pub type ContractPredicateIfContext<'input> = BaseParserRuleContext<'input,ContractPredicateIfContextExt<'input>>;

pub trait ContractPredicateIfContextAttrs<'input>: LibSLParserContext<'input>{
	fn ifPredicate(&self) -> Option<Rc<IfPredicateContextAll<'input>>> where Self:Sized{
		self.child_of_type(0)
	}
}

impl<'input> ContractPredicateIfContextAttrs<'input> for ContractPredicateIfContext<'input>{}

pub struct ContractPredicateIfContextExt<'input>{
	__base:ContractPredicateContextExt<'input>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{ContractPredicateIfContextExt<'a>}

impl<'input> LibSLParserContext<'input> for ContractPredicateIfContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for ContractPredicateIfContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_ContractPredicateIf(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_ContractPredicateIf(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for ContractPredicateIfContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_contractPredicate }
	//fn type_rule_index() -> usize where Self: Sized { RULE_contractPredicate }
}

impl<'input> Borrow<ContractPredicateContextExt<'input>> for ContractPredicateIfContext<'input>{
	fn borrow(&self) -> &ContractPredicateContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<ContractPredicateContextExt<'input>> for ContractPredicateIfContext<'input>{
	fn borrow_mut(&mut self) -> &mut ContractPredicateContextExt<'input> { &mut self.__base }
}

impl<'input> ContractPredicateContextAttrs<'input> for ContractPredicateIfContext<'input> {}

impl<'input> ContractPredicateIfContextExt<'input>{
	fn new(ctx: &dyn ContractPredicateContextAttrs<'input>) -> Rc<ContractPredicateContextAll<'input>>  {
		Rc::new(
			ContractPredicateContextAll::ContractPredicateIfContext(
				BaseParserRuleContext::copy_from(ctx,ContractPredicateIfContextExt{
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type ContractPredicateBlockContext<'input> = BaseParserRuleContext<'input,ContractPredicateBlockContextExt<'input>>;

pub trait ContractPredicateBlockContextAttrs<'input>: LibSLParserContext<'input>{
	fn blockPredicate(&self) -> Option<Rc<BlockPredicateContextAll<'input>>> where Self:Sized{
		self.child_of_type(0)
	}
}

impl<'input> ContractPredicateBlockContextAttrs<'input> for ContractPredicateBlockContext<'input>{}

pub struct ContractPredicateBlockContextExt<'input>{
	__base:ContractPredicateContextExt<'input>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{ContractPredicateBlockContextExt<'a>}

impl<'input> LibSLParserContext<'input> for ContractPredicateBlockContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for ContractPredicateBlockContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_ContractPredicateBlock(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_ContractPredicateBlock(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for ContractPredicateBlockContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_contractPredicate }
	//fn type_rule_index() -> usize where Self: Sized { RULE_contractPredicate }
}

impl<'input> Borrow<ContractPredicateContextExt<'input>> for ContractPredicateBlockContext<'input>{
	fn borrow(&self) -> &ContractPredicateContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<ContractPredicateContextExt<'input>> for ContractPredicateBlockContext<'input>{
	fn borrow_mut(&mut self) -> &mut ContractPredicateContextExt<'input> { &mut self.__base }
}

impl<'input> ContractPredicateContextAttrs<'input> for ContractPredicateBlockContext<'input> {}

impl<'input> ContractPredicateBlockContextExt<'input>{
	fn new(ctx: &dyn ContractPredicateContextAttrs<'input>) -> Rc<ContractPredicateContextAll<'input>>  {
		Rc::new(
			ContractPredicateContextAll::ContractPredicateBlockContext(
				BaseParserRuleContext::copy_from(ctx,ContractPredicateBlockContextExt{
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type ContractPredicateExprContext<'input> = BaseParserRuleContext<'input,ContractPredicateExprContextExt<'input>>;

pub trait ContractPredicateExprContextAttrs<'input>: LibSLParserContext<'input>{
	fn expr(&self) -> Option<Rc<ExprContextAll<'input>>> where Self:Sized{
		self.child_of_type(0)
	}
	/// Retrieves first TerminalNode corresponding to token SEMICOLON
	/// Returns `None` if there is no child corresponding to token SEMICOLON
	fn SEMICOLON(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(SEMICOLON, 0)
	}
}

impl<'input> ContractPredicateExprContextAttrs<'input> for ContractPredicateExprContext<'input>{}

pub struct ContractPredicateExprContextExt<'input>{
	__base:ContractPredicateContextExt<'input>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{ContractPredicateExprContextExt<'a>}

impl<'input> LibSLParserContext<'input> for ContractPredicateExprContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for ContractPredicateExprContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_ContractPredicateExpr(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_ContractPredicateExpr(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for ContractPredicateExprContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_contractPredicate }
	//fn type_rule_index() -> usize where Self: Sized { RULE_contractPredicate }
}

impl<'input> Borrow<ContractPredicateContextExt<'input>> for ContractPredicateExprContext<'input>{
	fn borrow(&self) -> &ContractPredicateContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<ContractPredicateContextExt<'input>> for ContractPredicateExprContext<'input>{
	fn borrow_mut(&mut self) -> &mut ContractPredicateContextExt<'input> { &mut self.__base }
}

impl<'input> ContractPredicateContextAttrs<'input> for ContractPredicateExprContext<'input> {}

impl<'input> ContractPredicateExprContextExt<'input>{
	fn new(ctx: &dyn ContractPredicateContextAttrs<'input>) -> Rc<ContractPredicateContextAll<'input>>  {
		Rc::new(
			ContractPredicateContextAll::ContractPredicateExprContext(
				BaseParserRuleContext::copy_from(ctx,ContractPredicateExprContextExt{
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

impl<'input, I, H> LibSLParser<'input, I, H>
where
    I: TokenStream<'input, TF = LocalTokenFactory<'input> > + TidAble<'input>,
    H: ErrorStrategy<'input,BaseParserType<'input,I>>
{
	pub fn contractPredicate(&mut self,)
	-> Result<Rc<ContractPredicateContextAll<'input>>,ANTLRError> {
		let mut recog = self;
		let _parentctx = recog.ctx.take();
		let mut _localctx = ContractPredicateContextExt::new(_parentctx.clone(), recog.base.get_state());
        recog.base.enter_rule(_localctx.clone(), 110, RULE_contractPredicate);
        let mut _localctx: Rc<ContractPredicateContextAll> = _localctx;
		let result: Result<(), ANTLRError> = (|| {

			recog.base.set_state(871);
			recog.err_handler.sync(&mut recog.base)?;
			match  recog.interpreter.adaptive_predict(111,&mut recog.base)? {
				1 =>{
					let tmp = ContractPredicateBlockContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 1);
					_localctx = tmp;
					{
					/*InvokeRule blockPredicate*/
					recog.base.set_state(866);
					recog.blockPredicate()?;

					}
				}
			,
				2 =>{
					let tmp = ContractPredicateIfContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 2);
					_localctx = tmp;
					{
					/*InvokeRule ifPredicate*/
					recog.base.set_state(867);
					recog.ifPredicate()?;

					}
				}
			,
				3 =>{
					let tmp = ContractPredicateExprContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 3);
					_localctx = tmp;
					{
					/*InvokeRule expr*/
					recog.base.set_state(868);
					recog.expr_rec(0)?;

					recog.base.set_state(869);
					recog.base.match_token(SEMICOLON,&mut recog.err_handler)?;

					}
				}

				_ => {}
			}
			Ok(())
		})();
		match result {
		Ok(_)=>{},
        Err(e @ ANTLRError::FallThrough(_)) => return Err(e),
		Err(ref re) => {
				//_localctx.exception = re;
				recog.err_handler.report_error(&mut recog.base, re);
				recog.err_handler.recover(&mut recog.base, re)?;
			}
		}
		recog.base.exit_rule();

		Ok(_localctx)
	}
}
//------------------- exprPredicate ----------------
#[derive(Debug)]
pub enum ExprPredicateContextAll<'input>{
	ExprPredicateBlockContext(ExprPredicateBlockContext<'input>),
	ExprPredicateExprContext(ExprPredicateExprContext<'input>),
Error(ExprPredicateContext<'input>)
}
antlr_rust::tid!{ExprPredicateContextAll<'a>}

impl<'input> antlr_rust::parser_rule_context::DerefSeal for ExprPredicateContextAll<'input>{}

impl<'input> LibSLParserContext<'input> for ExprPredicateContextAll<'input>{}

impl<'input> Deref for ExprPredicateContextAll<'input>{
	type Target = dyn ExprPredicateContextAttrs<'input> + 'input;
	fn deref(&self) -> &Self::Target{
		use ExprPredicateContextAll::*;
		match self{
			ExprPredicateBlockContext(inner) => inner,
			ExprPredicateExprContext(inner) => inner,
Error(inner) => inner
		}
	}
}
impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for ExprPredicateContextAll<'input>{
    fn enter(&self, listener: &mut (dyn LibSLParserListener<'input> + 'a)) { self.deref().enter(listener) }
    fn exit(&self, listener: &mut (dyn LibSLParserListener<'input> + 'a)) { self.deref().exit(listener) }
}



pub type ExprPredicateContext<'input> = BaseParserRuleContext<'input,ExprPredicateContextExt<'input>>;

#[derive(Clone)]
pub struct ExprPredicateContextExt<'input>{
ph:PhantomData<&'input str>
}

impl<'input> LibSLParserContext<'input> for ExprPredicateContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for ExprPredicateContext<'input>{
}

impl<'input> CustomRuleContext<'input> for ExprPredicateContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_exprPredicate }
	//fn type_rule_index() -> usize where Self: Sized { RULE_exprPredicate }
}
antlr_rust::tid!{ExprPredicateContextExt<'a>}

impl<'input> ExprPredicateContextExt<'input>{
	fn new(parent: Option<Rc<dyn LibSLParserContext<'input> + 'input > >, invoking_state: isize) -> Rc<ExprPredicateContextAll<'input>> {
		Rc::new(
		ExprPredicateContextAll::Error(
			BaseParserRuleContext::new_parser_ctx(parent, invoking_state,ExprPredicateContextExt{
				ph:PhantomData
			}),
		)
		)
	}
}

pub trait ExprPredicateContextAttrs<'input>: LibSLParserContext<'input> + BorrowMut<ExprPredicateContextExt<'input>>{


}

impl<'input> ExprPredicateContextAttrs<'input> for ExprPredicateContext<'input>{}

pub type ExprPredicateBlockContext<'input> = BaseParserRuleContext<'input,ExprPredicateBlockContextExt<'input>>;

pub trait ExprPredicateBlockContextAttrs<'input>: LibSLParserContext<'input>{
	fn blockPredicate(&self) -> Option<Rc<BlockPredicateContextAll<'input>>> where Self:Sized{
		self.child_of_type(0)
	}
}

impl<'input> ExprPredicateBlockContextAttrs<'input> for ExprPredicateBlockContext<'input>{}

pub struct ExprPredicateBlockContextExt<'input>{
	__base:ExprPredicateContextExt<'input>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{ExprPredicateBlockContextExt<'a>}

impl<'input> LibSLParserContext<'input> for ExprPredicateBlockContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for ExprPredicateBlockContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_ExprPredicateBlock(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_ExprPredicateBlock(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for ExprPredicateBlockContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_exprPredicate }
	//fn type_rule_index() -> usize where Self: Sized { RULE_exprPredicate }
}

impl<'input> Borrow<ExprPredicateContextExt<'input>> for ExprPredicateBlockContext<'input>{
	fn borrow(&self) -> &ExprPredicateContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<ExprPredicateContextExt<'input>> for ExprPredicateBlockContext<'input>{
	fn borrow_mut(&mut self) -> &mut ExprPredicateContextExt<'input> { &mut self.__base }
}

impl<'input> ExprPredicateContextAttrs<'input> for ExprPredicateBlockContext<'input> {}

impl<'input> ExprPredicateBlockContextExt<'input>{
	fn new(ctx: &dyn ExprPredicateContextAttrs<'input>) -> Rc<ExprPredicateContextAll<'input>>  {
		Rc::new(
			ExprPredicateContextAll::ExprPredicateBlockContext(
				BaseParserRuleContext::copy_from(ctx,ExprPredicateBlockContextExt{
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type ExprPredicateExprContext<'input> = BaseParserRuleContext<'input,ExprPredicateExprContextExt<'input>>;

pub trait ExprPredicateExprContextAttrs<'input>: LibSLParserContext<'input>{
	fn expr(&self) -> Option<Rc<ExprContextAll<'input>>> where Self:Sized{
		self.child_of_type(0)
	}
}

impl<'input> ExprPredicateExprContextAttrs<'input> for ExprPredicateExprContext<'input>{}

pub struct ExprPredicateExprContextExt<'input>{
	__base:ExprPredicateContextExt<'input>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{ExprPredicateExprContextExt<'a>}

impl<'input> LibSLParserContext<'input> for ExprPredicateExprContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for ExprPredicateExprContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_ExprPredicateExpr(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_ExprPredicateExpr(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for ExprPredicateExprContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_exprPredicate }
	//fn type_rule_index() -> usize where Self: Sized { RULE_exprPredicate }
}

impl<'input> Borrow<ExprPredicateContextExt<'input>> for ExprPredicateExprContext<'input>{
	fn borrow(&self) -> &ExprPredicateContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<ExprPredicateContextExt<'input>> for ExprPredicateExprContext<'input>{
	fn borrow_mut(&mut self) -> &mut ExprPredicateContextExt<'input> { &mut self.__base }
}

impl<'input> ExprPredicateContextAttrs<'input> for ExprPredicateExprContext<'input> {}

impl<'input> ExprPredicateExprContextExt<'input>{
	fn new(ctx: &dyn ExprPredicateContextAttrs<'input>) -> Rc<ExprPredicateContextAll<'input>>  {
		Rc::new(
			ExprPredicateContextAll::ExprPredicateExprContext(
				BaseParserRuleContext::copy_from(ctx,ExprPredicateExprContextExt{
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

impl<'input, I, H> LibSLParser<'input, I, H>
where
    I: TokenStream<'input, TF = LocalTokenFactory<'input> > + TidAble<'input>,
    H: ErrorStrategy<'input,BaseParserType<'input,I>>
{
	pub fn exprPredicate(&mut self,)
	-> Result<Rc<ExprPredicateContextAll<'input>>,ANTLRError> {
		let mut recog = self;
		let _parentctx = recog.ctx.take();
		let mut _localctx = ExprPredicateContextExt::new(_parentctx.clone(), recog.base.get_state());
        recog.base.enter_rule(_localctx.clone(), 112, RULE_exprPredicate);
        let mut _localctx: Rc<ExprPredicateContextAll> = _localctx;
		let result: Result<(), ANTLRError> = (|| {

			recog.base.set_state(875);
			recog.err_handler.sync(&mut recog.base)?;
			match  recog.interpreter.adaptive_predict(112,&mut recog.base)? {
				1 =>{
					let tmp = ExprPredicateBlockContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 1);
					_localctx = tmp;
					{
					/*InvokeRule blockPredicate*/
					recog.base.set_state(873);
					recog.blockPredicate()?;

					}
				}
			,
				2 =>{
					let tmp = ExprPredicateExprContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 2);
					_localctx = tmp;
					{
					/*InvokeRule expr*/
					recog.base.set_state(874);
					recog.expr_rec(0)?;

					}
				}

				_ => {}
			}
			Ok(())
		})();
		match result {
		Ok(_)=>{},
        Err(e @ ANTLRError::FallThrough(_)) => return Err(e),
		Err(ref re) => {
				//_localctx.exception = re;
				recog.err_handler.report_error(&mut recog.base, re);
				recog.err_handler.recover(&mut recog.base, re)?;
			}
		}
		recog.base.exit_rule();

		Ok(_localctx)
	}
}
//------------------- predicate ----------------
#[derive(Debug)]
pub enum PredicateContextAll<'input>{
	PredicateExprContext(PredicateExprContext<'input>),
	PredicateNamedContext(PredicateNamedContext<'input>),
	PredicateIfContext(PredicateIfContext<'input>),
	PredicateVariableDeclContext(PredicateVariableDeclContext<'input>),
	PredicateBlockContext(PredicateBlockContext<'input>),
Error(PredicateContext<'input>)
}
antlr_rust::tid!{PredicateContextAll<'a>}

impl<'input> antlr_rust::parser_rule_context::DerefSeal for PredicateContextAll<'input>{}

impl<'input> LibSLParserContext<'input> for PredicateContextAll<'input>{}

impl<'input> Deref for PredicateContextAll<'input>{
	type Target = dyn PredicateContextAttrs<'input> + 'input;
	fn deref(&self) -> &Self::Target{
		use PredicateContextAll::*;
		match self{
			PredicateExprContext(inner) => inner,
			PredicateNamedContext(inner) => inner,
			PredicateIfContext(inner) => inner,
			PredicateVariableDeclContext(inner) => inner,
			PredicateBlockContext(inner) => inner,
Error(inner) => inner
		}
	}
}
impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for PredicateContextAll<'input>{
    fn enter(&self, listener: &mut (dyn LibSLParserListener<'input> + 'a)) { self.deref().enter(listener) }
    fn exit(&self, listener: &mut (dyn LibSLParserListener<'input> + 'a)) { self.deref().exit(listener) }
}



pub type PredicateContext<'input> = BaseParserRuleContext<'input,PredicateContextExt<'input>>;

#[derive(Clone)]
pub struct PredicateContextExt<'input>{
ph:PhantomData<&'input str>
}

impl<'input> LibSLParserContext<'input> for PredicateContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for PredicateContext<'input>{
}

impl<'input> CustomRuleContext<'input> for PredicateContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_predicate }
	//fn type_rule_index() -> usize where Self: Sized { RULE_predicate }
}
antlr_rust::tid!{PredicateContextExt<'a>}

impl<'input> PredicateContextExt<'input>{
	fn new(parent: Option<Rc<dyn LibSLParserContext<'input> + 'input > >, invoking_state: isize) -> Rc<PredicateContextAll<'input>> {
		Rc::new(
		PredicateContextAll::Error(
			BaseParserRuleContext::new_parser_ctx(parent, invoking_state,PredicateContextExt{
				ph:PhantomData
			}),
		)
		)
	}
}

pub trait PredicateContextAttrs<'input>: LibSLParserContext<'input> + BorrowMut<PredicateContextExt<'input>>{


}

impl<'input> PredicateContextAttrs<'input> for PredicateContext<'input>{}

pub type PredicateExprContext<'input> = BaseParserRuleContext<'input,PredicateExprContextExt<'input>>;

pub trait PredicateExprContextAttrs<'input>: LibSLParserContext<'input>{
	fn expr(&self) -> Option<Rc<ExprContextAll<'input>>> where Self:Sized{
		self.child_of_type(0)
	}
	/// Retrieves first TerminalNode corresponding to token SEMICOLON
	/// Returns `None` if there is no child corresponding to token SEMICOLON
	fn SEMICOLON(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(SEMICOLON, 0)
	}
}

impl<'input> PredicateExprContextAttrs<'input> for PredicateExprContext<'input>{}

pub struct PredicateExprContextExt<'input>{
	__base:PredicateContextExt<'input>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{PredicateExprContextExt<'a>}

impl<'input> LibSLParserContext<'input> for PredicateExprContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for PredicateExprContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_PredicateExpr(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_PredicateExpr(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for PredicateExprContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_predicate }
	//fn type_rule_index() -> usize where Self: Sized { RULE_predicate }
}

impl<'input> Borrow<PredicateContextExt<'input>> for PredicateExprContext<'input>{
	fn borrow(&self) -> &PredicateContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<PredicateContextExt<'input>> for PredicateExprContext<'input>{
	fn borrow_mut(&mut self) -> &mut PredicateContextExt<'input> { &mut self.__base }
}

impl<'input> PredicateContextAttrs<'input> for PredicateExprContext<'input> {}

impl<'input> PredicateExprContextExt<'input>{
	fn new(ctx: &dyn PredicateContextAttrs<'input>) -> Rc<PredicateContextAll<'input>>  {
		Rc::new(
			PredicateContextAll::PredicateExprContext(
				BaseParserRuleContext::copy_from(ctx,PredicateExprContextExt{
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type PredicateNamedContext<'input> = BaseParserRuleContext<'input,PredicateNamedContextExt<'input>>;

pub trait PredicateNamedContextAttrs<'input>: LibSLParserContext<'input>{
	/// Retrieves first TerminalNode corresponding to token COLON
	/// Returns `None` if there is no child corresponding to token COLON
	fn COLON(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(COLON, 0)
	}
	fn predicate(&self) -> Option<Rc<PredicateContextAll<'input>>> where Self:Sized{
		self.child_of_type(0)
	}
	fn ident(&self) -> Option<Rc<IdentContextAll<'input>>> where Self:Sized{
		self.child_of_type(0)
	}
}

impl<'input> PredicateNamedContextAttrs<'input> for PredicateNamedContext<'input>{}

pub struct PredicateNamedContextExt<'input>{
	__base:PredicateContextExt<'input>,
	pub name: Option<Rc<IdentContextAll<'input>>>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{PredicateNamedContextExt<'a>}

impl<'input> LibSLParserContext<'input> for PredicateNamedContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for PredicateNamedContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_PredicateNamed(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_PredicateNamed(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for PredicateNamedContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_predicate }
	//fn type_rule_index() -> usize where Self: Sized { RULE_predicate }
}

impl<'input> Borrow<PredicateContextExt<'input>> for PredicateNamedContext<'input>{
	fn borrow(&self) -> &PredicateContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<PredicateContextExt<'input>> for PredicateNamedContext<'input>{
	fn borrow_mut(&mut self) -> &mut PredicateContextExt<'input> { &mut self.__base }
}

impl<'input> PredicateContextAttrs<'input> for PredicateNamedContext<'input> {}

impl<'input> PredicateNamedContextExt<'input>{
	fn new(ctx: &dyn PredicateContextAttrs<'input>) -> Rc<PredicateContextAll<'input>>  {
		Rc::new(
			PredicateContextAll::PredicateNamedContext(
				BaseParserRuleContext::copy_from(ctx,PredicateNamedContextExt{
        			name:None, 
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type PredicateIfContext<'input> = BaseParserRuleContext<'input,PredicateIfContextExt<'input>>;

pub trait PredicateIfContextAttrs<'input>: LibSLParserContext<'input>{
	fn ifPredicate(&self) -> Option<Rc<IfPredicateContextAll<'input>>> where Self:Sized{
		self.child_of_type(0)
	}
}

impl<'input> PredicateIfContextAttrs<'input> for PredicateIfContext<'input>{}

pub struct PredicateIfContextExt<'input>{
	__base:PredicateContextExt<'input>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{PredicateIfContextExt<'a>}

impl<'input> LibSLParserContext<'input> for PredicateIfContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for PredicateIfContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_PredicateIf(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_PredicateIf(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for PredicateIfContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_predicate }
	//fn type_rule_index() -> usize where Self: Sized { RULE_predicate }
}

impl<'input> Borrow<PredicateContextExt<'input>> for PredicateIfContext<'input>{
	fn borrow(&self) -> &PredicateContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<PredicateContextExt<'input>> for PredicateIfContext<'input>{
	fn borrow_mut(&mut self) -> &mut PredicateContextExt<'input> { &mut self.__base }
}

impl<'input> PredicateContextAttrs<'input> for PredicateIfContext<'input> {}

impl<'input> PredicateIfContextExt<'input>{
	fn new(ctx: &dyn PredicateContextAttrs<'input>) -> Rc<PredicateContextAll<'input>>  {
		Rc::new(
			PredicateContextAll::PredicateIfContext(
				BaseParserRuleContext::copy_from(ctx,PredicateIfContextExt{
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type PredicateVariableDeclContext<'input> = BaseParserRuleContext<'input,PredicateVariableDeclContextExt<'input>>;

pub trait PredicateVariableDeclContextAttrs<'input>: LibSLParserContext<'input>{
	fn variableDecl(&self) -> Option<Rc<VariableDeclContextAll<'input>>> where Self:Sized{
		self.child_of_type(0)
	}
}

impl<'input> PredicateVariableDeclContextAttrs<'input> for PredicateVariableDeclContext<'input>{}

pub struct PredicateVariableDeclContextExt<'input>{
	__base:PredicateContextExt<'input>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{PredicateVariableDeclContextExt<'a>}

impl<'input> LibSLParserContext<'input> for PredicateVariableDeclContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for PredicateVariableDeclContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_PredicateVariableDecl(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_PredicateVariableDecl(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for PredicateVariableDeclContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_predicate }
	//fn type_rule_index() -> usize where Self: Sized { RULE_predicate }
}

impl<'input> Borrow<PredicateContextExt<'input>> for PredicateVariableDeclContext<'input>{
	fn borrow(&self) -> &PredicateContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<PredicateContextExt<'input>> for PredicateVariableDeclContext<'input>{
	fn borrow_mut(&mut self) -> &mut PredicateContextExt<'input> { &mut self.__base }
}

impl<'input> PredicateContextAttrs<'input> for PredicateVariableDeclContext<'input> {}

impl<'input> PredicateVariableDeclContextExt<'input>{
	fn new(ctx: &dyn PredicateContextAttrs<'input>) -> Rc<PredicateContextAll<'input>>  {
		Rc::new(
			PredicateContextAll::PredicateVariableDeclContext(
				BaseParserRuleContext::copy_from(ctx,PredicateVariableDeclContextExt{
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type PredicateBlockContext<'input> = BaseParserRuleContext<'input,PredicateBlockContextExt<'input>>;

pub trait PredicateBlockContextAttrs<'input>: LibSLParserContext<'input>{
	fn blockPredicate(&self) -> Option<Rc<BlockPredicateContextAll<'input>>> where Self:Sized{
		self.child_of_type(0)
	}
}

impl<'input> PredicateBlockContextAttrs<'input> for PredicateBlockContext<'input>{}

pub struct PredicateBlockContextExt<'input>{
	__base:PredicateContextExt<'input>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{PredicateBlockContextExt<'a>}

impl<'input> LibSLParserContext<'input> for PredicateBlockContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for PredicateBlockContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_PredicateBlock(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_PredicateBlock(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for PredicateBlockContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_predicate }
	//fn type_rule_index() -> usize where Self: Sized { RULE_predicate }
}

impl<'input> Borrow<PredicateContextExt<'input>> for PredicateBlockContext<'input>{
	fn borrow(&self) -> &PredicateContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<PredicateContextExt<'input>> for PredicateBlockContext<'input>{
	fn borrow_mut(&mut self) -> &mut PredicateContextExt<'input> { &mut self.__base }
}

impl<'input> PredicateContextAttrs<'input> for PredicateBlockContext<'input> {}

impl<'input> PredicateBlockContextExt<'input>{
	fn new(ctx: &dyn PredicateContextAttrs<'input>) -> Rc<PredicateContextAll<'input>>  {
		Rc::new(
			PredicateContextAll::PredicateBlockContext(
				BaseParserRuleContext::copy_from(ctx,PredicateBlockContextExt{
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

impl<'input, I, H> LibSLParser<'input, I, H>
where
    I: TokenStream<'input, TF = LocalTokenFactory<'input> > + TidAble<'input>,
    H: ErrorStrategy<'input,BaseParserType<'input,I>>
{
	pub fn predicate(&mut self,)
	-> Result<Rc<PredicateContextAll<'input>>,ANTLRError> {
		let mut recog = self;
		let _parentctx = recog.ctx.take();
		let mut _localctx = PredicateContextExt::new(_parentctx.clone(), recog.base.get_state());
        recog.base.enter_rule(_localctx.clone(), 114, RULE_predicate);
        let mut _localctx: Rc<PredicateContextAll> = _localctx;
		let result: Result<(), ANTLRError> = (|| {

			recog.base.set_state(887);
			recog.err_handler.sync(&mut recog.base)?;
			match  recog.interpreter.adaptive_predict(113,&mut recog.base)? {
				1 =>{
					let tmp = PredicateBlockContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 1);
					_localctx = tmp;
					{
					/*InvokeRule blockPredicate*/
					recog.base.set_state(877);
					recog.blockPredicate()?;

					}
				}
			,
				2 =>{
					let tmp = PredicateNamedContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 2);
					_localctx = tmp;
					{
					/*InvokeRule ident*/
					recog.base.set_state(878);
					let tmp = recog.ident()?;
					if let PredicateContextAll::PredicateNamedContext(ctx) = cast_mut::<_,PredicateContextAll >(&mut _localctx){
					ctx.name = Some(tmp.clone()); } else {unreachable!("cant cast");}  

					recog.base.set_state(879);
					recog.base.match_token(COLON,&mut recog.err_handler)?;

					/*InvokeRule predicate*/
					recog.base.set_state(880);
					recog.predicate()?;

					}
				}
			,
				3 =>{
					let tmp = PredicateVariableDeclContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 3);
					_localctx = tmp;
					{
					/*InvokeRule variableDecl*/
					recog.base.set_state(882);
					recog.variableDecl()?;

					}
				}
			,
				4 =>{
					let tmp = PredicateIfContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 4);
					_localctx = tmp;
					{
					/*InvokeRule ifPredicate*/
					recog.base.set_state(883);
					recog.ifPredicate()?;

					}
				}
			,
				5 =>{
					let tmp = PredicateExprContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 5);
					_localctx = tmp;
					{
					/*InvokeRule expr*/
					recog.base.set_state(884);
					recog.expr_rec(0)?;

					recog.base.set_state(885);
					recog.base.match_token(SEMICOLON,&mut recog.err_handler)?;

					}
				}

				_ => {}
			}
			Ok(())
		})();
		match result {
		Ok(_)=>{},
        Err(e @ ANTLRError::FallThrough(_)) => return Err(e),
		Err(ref re) => {
				//_localctx.exception = re;
				recog.err_handler.report_error(&mut recog.base, re);
				recog.err_handler.recover(&mut recog.base, re)?;
			}
		}
		recog.base.exit_rule();

		Ok(_localctx)
	}
}
//------------------- blockPredicate ----------------
pub type BlockPredicateContextAll<'input> = BlockPredicateContext<'input>;


pub type BlockPredicateContext<'input> = BaseParserRuleContext<'input,BlockPredicateContextExt<'input>>;

#[derive(Clone)]
pub struct BlockPredicateContextExt<'input>{
	pub predicate: Option<Rc<PredicateContextAll<'input>>>,
	pub predicates:Vec<Rc<PredicateContextAll<'input>>>,
ph:PhantomData<&'input str>
}

impl<'input> LibSLParserContext<'input> for BlockPredicateContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for BlockPredicateContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_blockPredicate(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_blockPredicate(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for BlockPredicateContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_blockPredicate }
	//fn type_rule_index() -> usize where Self: Sized { RULE_blockPredicate }
}
antlr_rust::tid!{BlockPredicateContextExt<'a>}

impl<'input> BlockPredicateContextExt<'input>{
	fn new(parent: Option<Rc<dyn LibSLParserContext<'input> + 'input > >, invoking_state: isize) -> Rc<BlockPredicateContextAll<'input>> {
		Rc::new(
			BaseParserRuleContext::new_parser_ctx(parent, invoking_state,BlockPredicateContextExt{
				predicate: None, 
				predicates: Vec::new(), 
				ph:PhantomData
			}),
		)
	}
}

pub trait BlockPredicateContextAttrs<'input>: LibSLParserContext<'input> + BorrowMut<BlockPredicateContextExt<'input>>{

/// Retrieves first TerminalNode corresponding to token L_BRACE
/// Returns `None` if there is no child corresponding to token L_BRACE
fn L_BRACE(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(L_BRACE, 0)
}
/// Retrieves first TerminalNode corresponding to token R_BRACE
/// Returns `None` if there is no child corresponding to token R_BRACE
fn R_BRACE(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(R_BRACE, 0)
}
fn predicate_all(&self) ->  Vec<Rc<PredicateContextAll<'input>>> where Self:Sized{
	self.children_of_type()
}
fn predicate(&self, i: usize) -> Option<Rc<PredicateContextAll<'input>>> where Self:Sized{
	self.child_of_type(i)
}

}

impl<'input> BlockPredicateContextAttrs<'input> for BlockPredicateContext<'input>{}

impl<'input, I, H> LibSLParser<'input, I, H>
where
    I: TokenStream<'input, TF = LocalTokenFactory<'input> > + TidAble<'input>,
    H: ErrorStrategy<'input,BaseParserType<'input,I>>
{
	pub fn blockPredicate(&mut self,)
	-> Result<Rc<BlockPredicateContextAll<'input>>,ANTLRError> {
		let mut recog = self;
		let _parentctx = recog.ctx.take();
		let mut _localctx = BlockPredicateContextExt::new(_parentctx.clone(), recog.base.get_state());
        recog.base.enter_rule(_localctx.clone(), 116, RULE_blockPredicate);
        let mut _localctx: Rc<BlockPredicateContextAll> = _localctx;
		let mut _la: isize = -1;
		let result: Result<(), ANTLRError> = (|| {

			//recog.base.enter_outer_alt(_localctx.clone(), 1);
			recog.base.enter_outer_alt(None, 1);
			{
			recog.base.set_state(889);
			recog.base.match_token(L_BRACE,&mut recog.err_handler)?;

			recog.base.set_state(893);
			recog.err_handler.sync(&mut recog.base)?;
			_la = recog.base.input.la(1);
			while (((_la) & !0x3f) == 0 && ((1usize << _la) & 68682064) != 0) || ((((_la - 35)) & !0x3f) == 0 && ((1usize << (_la - 35)) & 281018369) != 0) || ((((_la - 69)) & !0x3f) == 0 && ((1usize << (_la - 69)) & 529404081) != 0) {
				{
				{
				/*InvokeRule predicate*/
				recog.base.set_state(890);
				let tmp = recog.predicate()?;
				 cast_mut::<_,BlockPredicateContext >(&mut _localctx).predicate = Some(tmp.clone());
				  

				let temp =  cast_mut::<_,BlockPredicateContext >(&mut _localctx).predicate.clone().unwrap()
				 ;
				 cast_mut::<_,BlockPredicateContext >(&mut _localctx).predicates.push(temp);
				  
				}
				}
				recog.base.set_state(895);
				recog.err_handler.sync(&mut recog.base)?;
				_la = recog.base.input.la(1);
			}
			recog.base.set_state(896);
			recog.base.match_token(R_BRACE,&mut recog.err_handler)?;

			}
			Ok(())
		})();
		match result {
		Ok(_)=>{},
        Err(e @ ANTLRError::FallThrough(_)) => return Err(e),
		Err(ref re) => {
				//_localctx.exception = re;
				recog.err_handler.report_error(&mut recog.base, re);
				recog.err_handler.recover(&mut recog.base, re)?;
			}
		}
		recog.base.exit_rule();

		Ok(_localctx)
	}
}
//------------------- ifPredicate ----------------
pub type IfPredicateContextAll<'input> = IfPredicateContext<'input>;


pub type IfPredicateContext<'input> = BaseParserRuleContext<'input,IfPredicateContextExt<'input>>;

#[derive(Clone)]
pub struct IfPredicateContextExt<'input>{
	pub condition: Option<Rc<ExprContextAll<'input>>>,
	pub thenBranch: Option<Rc<PredicateContextAll<'input>>>,
	pub elseBranch: Option<Rc<PredicateContextAll<'input>>>,
ph:PhantomData<&'input str>
}

impl<'input> LibSLParserContext<'input> for IfPredicateContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for IfPredicateContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_ifPredicate(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_ifPredicate(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for IfPredicateContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_ifPredicate }
	//fn type_rule_index() -> usize where Self: Sized { RULE_ifPredicate }
}
antlr_rust::tid!{IfPredicateContextExt<'a>}

impl<'input> IfPredicateContextExt<'input>{
	fn new(parent: Option<Rc<dyn LibSLParserContext<'input> + 'input > >, invoking_state: isize) -> Rc<IfPredicateContextAll<'input>> {
		Rc::new(
			BaseParserRuleContext::new_parser_ctx(parent, invoking_state,IfPredicateContextExt{
				condition: None, thenBranch: None, elseBranch: None, 
				ph:PhantomData
			}),
		)
	}
}

pub trait IfPredicateContextAttrs<'input>: LibSLParserContext<'input> + BorrowMut<IfPredicateContextExt<'input>>{

/// Retrieves first TerminalNode corresponding to token IF
/// Returns `None` if there is no child corresponding to token IF
fn IF(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(IF, 0)
}
/// Retrieves first TerminalNode corresponding to token L_PAREN
/// Returns `None` if there is no child corresponding to token L_PAREN
fn L_PAREN(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(L_PAREN, 0)
}
/// Retrieves first TerminalNode corresponding to token R_PAREN
/// Returns `None` if there is no child corresponding to token R_PAREN
fn R_PAREN(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(R_PAREN, 0)
}
fn expr(&self) -> Option<Rc<ExprContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}
fn predicate_all(&self) ->  Vec<Rc<PredicateContextAll<'input>>> where Self:Sized{
	self.children_of_type()
}
fn predicate(&self, i: usize) -> Option<Rc<PredicateContextAll<'input>>> where Self:Sized{
	self.child_of_type(i)
}
/// Retrieves first TerminalNode corresponding to token ELSE
/// Returns `None` if there is no child corresponding to token ELSE
fn ELSE(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(ELSE, 0)
}

}

impl<'input> IfPredicateContextAttrs<'input> for IfPredicateContext<'input>{}

impl<'input, I, H> LibSLParser<'input, I, H>
where
    I: TokenStream<'input, TF = LocalTokenFactory<'input> > + TidAble<'input>,
    H: ErrorStrategy<'input,BaseParserType<'input,I>>
{
	pub fn ifPredicate(&mut self,)
	-> Result<Rc<IfPredicateContextAll<'input>>,ANTLRError> {
		let mut recog = self;
		let _parentctx = recog.ctx.take();
		let mut _localctx = IfPredicateContextExt::new(_parentctx.clone(), recog.base.get_state());
        recog.base.enter_rule(_localctx.clone(), 118, RULE_ifPredicate);
        let mut _localctx: Rc<IfPredicateContextAll> = _localctx;
		let result: Result<(), ANTLRError> = (|| {

			//recog.base.enter_outer_alt(_localctx.clone(), 1);
			recog.base.enter_outer_alt(None, 1);
			{
			recog.base.set_state(898);
			recog.base.match_token(IF,&mut recog.err_handler)?;

			recog.base.set_state(899);
			recog.base.match_token(L_PAREN,&mut recog.err_handler)?;

			/*InvokeRule expr*/
			recog.base.set_state(900);
			let tmp = recog.expr_rec(0)?;
			 cast_mut::<_,IfPredicateContext >(&mut _localctx).condition = Some(tmp.clone());
			  

			recog.base.set_state(901);
			recog.base.match_token(R_PAREN,&mut recog.err_handler)?;

			/*InvokeRule predicate*/
			recog.base.set_state(902);
			let tmp = recog.predicate()?;
			 cast_mut::<_,IfPredicateContext >(&mut _localctx).thenBranch = Some(tmp.clone());
			  

			recog.base.set_state(905);
			recog.err_handler.sync(&mut recog.base)?;
			match  recog.interpreter.adaptive_predict(115,&mut recog.base)? {
				x if x == 1=>{
					{
					recog.base.set_state(903);
					recog.base.match_token(ELSE,&mut recog.err_handler)?;

					/*InvokeRule predicate*/
					recog.base.set_state(904);
					let tmp = recog.predicate()?;
					 cast_mut::<_,IfPredicateContext >(&mut _localctx).elseBranch = Some(tmp.clone());
					  

					}
				}

				_ => {}
			}
			}
			Ok(())
		})();
		match result {
		Ok(_)=>{},
        Err(e @ ANTLRError::FallThrough(_)) => return Err(e),
		Err(ref re) => {
				//_localctx.exception = re;
				recog.err_handler.report_error(&mut recog.base, re);
				recog.err_handler.recover(&mut recog.base, re)?;
			}
		}
		recog.base.exit_rule();

		Ok(_localctx)
	}
}
//------------------- annotation ----------------
pub type AnnotationContextAll<'input> = AnnotationContext<'input>;


pub type AnnotationContext<'input> = BaseParserRuleContext<'input,AnnotationContextExt<'input>>;

#[derive(Clone)]
pub struct AnnotationContextExt<'input>{
	pub name: Option<Rc<IdentContextAll<'input>>>,
	pub args: Option<Rc<AnnotationArgListContextAll<'input>>>,
ph:PhantomData<&'input str>
}

impl<'input> LibSLParserContext<'input> for AnnotationContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for AnnotationContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_annotation(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_annotation(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for AnnotationContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_annotation }
	//fn type_rule_index() -> usize where Self: Sized { RULE_annotation }
}
antlr_rust::tid!{AnnotationContextExt<'a>}

impl<'input> AnnotationContextExt<'input>{
	fn new(parent: Option<Rc<dyn LibSLParserContext<'input> + 'input > >, invoking_state: isize) -> Rc<AnnotationContextAll<'input>> {
		Rc::new(
			BaseParserRuleContext::new_parser_ctx(parent, invoking_state,AnnotationContextExt{
				name: None, args: None, 
				ph:PhantomData
			}),
		)
	}
}

pub trait AnnotationContextAttrs<'input>: LibSLParserContext<'input> + BorrowMut<AnnotationContextExt<'input>>{

/// Retrieves first TerminalNode corresponding to token AT
/// Returns `None` if there is no child corresponding to token AT
fn AT(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(AT, 0)
}
fn ident(&self) -> Option<Rc<IdentContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}
/// Retrieves first TerminalNode corresponding to token L_PAREN
/// Returns `None` if there is no child corresponding to token L_PAREN
fn L_PAREN(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(L_PAREN, 0)
}
/// Retrieves first TerminalNode corresponding to token R_PAREN
/// Returns `None` if there is no child corresponding to token R_PAREN
fn R_PAREN(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(R_PAREN, 0)
}
fn annotationArgList(&self) -> Option<Rc<AnnotationArgListContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}
/// Retrieves first TerminalNode corresponding to token COMMA
/// Returns `None` if there is no child corresponding to token COMMA
fn COMMA(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(COMMA, 0)
}

}

impl<'input> AnnotationContextAttrs<'input> for AnnotationContext<'input>{}

impl<'input, I, H> LibSLParser<'input, I, H>
where
    I: TokenStream<'input, TF = LocalTokenFactory<'input> > + TidAble<'input>,
    H: ErrorStrategy<'input,BaseParserType<'input,I>>
{
	pub fn annotation(&mut self,)
	-> Result<Rc<AnnotationContextAll<'input>>,ANTLRError> {
		let mut recog = self;
		let _parentctx = recog.ctx.take();
		let mut _localctx = AnnotationContextExt::new(_parentctx.clone(), recog.base.get_state());
        recog.base.enter_rule(_localctx.clone(), 120, RULE_annotation);
        let mut _localctx: Rc<AnnotationContextAll> = _localctx;
		let mut _la: isize = -1;
		let result: Result<(), ANTLRError> = (|| {

			//recog.base.enter_outer_alt(_localctx.clone(), 1);
			recog.base.enter_outer_alt(None, 1);
			{
			recog.base.set_state(907);
			recog.base.match_token(AT,&mut recog.err_handler)?;

			/*InvokeRule ident*/
			recog.base.set_state(908);
			let tmp = recog.ident()?;
			 cast_mut::<_,AnnotationContext >(&mut _localctx).name = Some(tmp.clone());
			  

			recog.base.set_state(917);
			recog.err_handler.sync(&mut recog.base)?;
			_la = recog.base.input.la(1);
			if _la==L_PAREN {
				{
				recog.base.set_state(909);
				recog.base.match_token(L_PAREN,&mut recog.err_handler)?;

				recog.base.set_state(914);
				recog.err_handler.sync(&mut recog.base)?;
				_la = recog.base.input.la(1);
				if (((_la) & !0x3f) == 0 && ((1usize << _la) & 68682064) != 0) || _la==TILDE || _la==NEW || ((((_la - 69)) & !0x3f) == 0 && ((1usize << (_la - 69)) & 512626737) != 0) {
					{
					/*InvokeRule annotationArgList*/
					recog.base.set_state(910);
					let tmp = recog.annotationArgList()?;
					 cast_mut::<_,AnnotationContext >(&mut _localctx).args = Some(tmp.clone());
					  

					recog.base.set_state(912);
					recog.err_handler.sync(&mut recog.base)?;
					_la = recog.base.input.la(1);
					if _la==COMMA {
						{
						recog.base.set_state(911);
						recog.base.match_token(COMMA,&mut recog.err_handler)?;

						}
					}

					}
				}

				recog.base.set_state(916);
				recog.base.match_token(R_PAREN,&mut recog.err_handler)?;

				}
			}

			}
			Ok(())
		})();
		match result {
		Ok(_)=>{},
        Err(e @ ANTLRError::FallThrough(_)) => return Err(e),
		Err(ref re) => {
				//_localctx.exception = re;
				recog.err_handler.report_error(&mut recog.base, re);
				recog.err_handler.recover(&mut recog.base, re)?;
			}
		}
		recog.base.exit_rule();

		Ok(_localctx)
	}
}
//------------------- annotationArgList ----------------
pub type AnnotationArgListContextAll<'input> = AnnotationArgListContext<'input>;


pub type AnnotationArgListContext<'input> = BaseParserRuleContext<'input,AnnotationArgListContextExt<'input>>;

#[derive(Clone)]
pub struct AnnotationArgListContextExt<'input>{
	pub annotationArg: Option<Rc<AnnotationArgContextAll<'input>>>,
	pub args:Vec<Rc<AnnotationArgContextAll<'input>>>,
ph:PhantomData<&'input str>
}

impl<'input> LibSLParserContext<'input> for AnnotationArgListContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for AnnotationArgListContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_annotationArgList(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_annotationArgList(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for AnnotationArgListContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_annotationArgList }
	//fn type_rule_index() -> usize where Self: Sized { RULE_annotationArgList }
}
antlr_rust::tid!{AnnotationArgListContextExt<'a>}

impl<'input> AnnotationArgListContextExt<'input>{
	fn new(parent: Option<Rc<dyn LibSLParserContext<'input> + 'input > >, invoking_state: isize) -> Rc<AnnotationArgListContextAll<'input>> {
		Rc::new(
			BaseParserRuleContext::new_parser_ctx(parent, invoking_state,AnnotationArgListContextExt{
				annotationArg: None, 
				args: Vec::new(), 
				ph:PhantomData
			}),
		)
	}
}

pub trait AnnotationArgListContextAttrs<'input>: LibSLParserContext<'input> + BorrowMut<AnnotationArgListContextExt<'input>>{

fn annotationArg_all(&self) ->  Vec<Rc<AnnotationArgContextAll<'input>>> where Self:Sized{
	self.children_of_type()
}
fn annotationArg(&self, i: usize) -> Option<Rc<AnnotationArgContextAll<'input>>> where Self:Sized{
	self.child_of_type(i)
}
/// Retrieves all `TerminalNode`s corresponding to token COMMA in current rule
fn COMMA_all(&self) -> Vec<Rc<TerminalNode<'input,LibSLParserContextType>>>  where Self:Sized{
	self.get_tokens(COMMA)
}
/// Retrieves 'i's TerminalNode corresponding to token COMMA, starting from 0.
/// Returns `None` if number of children corresponding to token COMMA is less or equal than `i`.
fn COMMA(&self, i: usize) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(COMMA, i)
}

}

impl<'input> AnnotationArgListContextAttrs<'input> for AnnotationArgListContext<'input>{}

impl<'input, I, H> LibSLParser<'input, I, H>
where
    I: TokenStream<'input, TF = LocalTokenFactory<'input> > + TidAble<'input>,
    H: ErrorStrategy<'input,BaseParserType<'input,I>>
{
	pub fn annotationArgList(&mut self,)
	-> Result<Rc<AnnotationArgListContextAll<'input>>,ANTLRError> {
		let mut recog = self;
		let _parentctx = recog.ctx.take();
		let mut _localctx = AnnotationArgListContextExt::new(_parentctx.clone(), recog.base.get_state());
        recog.base.enter_rule(_localctx.clone(), 122, RULE_annotationArgList);
        let mut _localctx: Rc<AnnotationArgListContextAll> = _localctx;
		let result: Result<(), ANTLRError> = (|| {

			let mut _alt: isize;
			//recog.base.enter_outer_alt(_localctx.clone(), 1);
			recog.base.enter_outer_alt(None, 1);
			{
			/*InvokeRule annotationArg*/
			recog.base.set_state(919);
			let tmp = recog.annotationArg()?;
			 cast_mut::<_,AnnotationArgListContext >(&mut _localctx).annotationArg = Some(tmp.clone());
			  

			let temp =  cast_mut::<_,AnnotationArgListContext >(&mut _localctx).annotationArg.clone().unwrap()
			 ;
			 cast_mut::<_,AnnotationArgListContext >(&mut _localctx).args.push(temp);
			  
			recog.base.set_state(924);
			recog.err_handler.sync(&mut recog.base)?;
			_alt = recog.interpreter.adaptive_predict(119,&mut recog.base)?;
			while { _alt!=2 && _alt!=INVALID_ALT } {
				if _alt==1 {
					{
					{
					recog.base.set_state(920);
					recog.base.match_token(COMMA,&mut recog.err_handler)?;

					/*InvokeRule annotationArg*/
					recog.base.set_state(921);
					let tmp = recog.annotationArg()?;
					 cast_mut::<_,AnnotationArgListContext >(&mut _localctx).annotationArg = Some(tmp.clone());
					  

					let temp =  cast_mut::<_,AnnotationArgListContext >(&mut _localctx).annotationArg.clone().unwrap()
					 ;
					 cast_mut::<_,AnnotationArgListContext >(&mut _localctx).args.push(temp);
					  
					}
					} 
				}
				recog.base.set_state(926);
				recog.err_handler.sync(&mut recog.base)?;
				_alt = recog.interpreter.adaptive_predict(119,&mut recog.base)?;
			}
			}
			Ok(())
		})();
		match result {
		Ok(_)=>{},
        Err(e @ ANTLRError::FallThrough(_)) => return Err(e),
		Err(ref re) => {
				//_localctx.exception = re;
				recog.err_handler.report_error(&mut recog.base, re);
				recog.err_handler.recover(&mut recog.base, re)?;
			}
		}
		recog.base.exit_rule();

		Ok(_localctx)
	}
}
//------------------- annotationArg ----------------
pub type AnnotationArgContextAll<'input> = AnnotationArgContext<'input>;


pub type AnnotationArgContext<'input> = BaseParserRuleContext<'input,AnnotationArgContextExt<'input>>;

#[derive(Clone)]
pub struct AnnotationArgContextExt<'input>{
	pub name: Option<Rc<IdentContextAll<'input>>>,
	pub value: Option<Rc<ExprContextAll<'input>>>,
ph:PhantomData<&'input str>
}

impl<'input> LibSLParserContext<'input> for AnnotationArgContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for AnnotationArgContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_annotationArg(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_annotationArg(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for AnnotationArgContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_annotationArg }
	//fn type_rule_index() -> usize where Self: Sized { RULE_annotationArg }
}
antlr_rust::tid!{AnnotationArgContextExt<'a>}

impl<'input> AnnotationArgContextExt<'input>{
	fn new(parent: Option<Rc<dyn LibSLParserContext<'input> + 'input > >, invoking_state: isize) -> Rc<AnnotationArgContextAll<'input>> {
		Rc::new(
			BaseParserRuleContext::new_parser_ctx(parent, invoking_state,AnnotationArgContextExt{
				name: None, value: None, 
				ph:PhantomData
			}),
		)
	}
}

pub trait AnnotationArgContextAttrs<'input>: LibSLParserContext<'input> + BorrowMut<AnnotationArgContextExt<'input>>{

fn expr(&self) -> Option<Rc<ExprContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}
/// Retrieves first TerminalNode corresponding to token EQ
/// Returns `None` if there is no child corresponding to token EQ
fn EQ(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(EQ, 0)
}
fn ident(&self) -> Option<Rc<IdentContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}

}

impl<'input> AnnotationArgContextAttrs<'input> for AnnotationArgContext<'input>{}

impl<'input, I, H> LibSLParser<'input, I, H>
where
    I: TokenStream<'input, TF = LocalTokenFactory<'input> > + TidAble<'input>,
    H: ErrorStrategy<'input,BaseParserType<'input,I>>
{
	pub fn annotationArg(&mut self,)
	-> Result<Rc<AnnotationArgContextAll<'input>>,ANTLRError> {
		let mut recog = self;
		let _parentctx = recog.ctx.take();
		let mut _localctx = AnnotationArgContextExt::new(_parentctx.clone(), recog.base.get_state());
        recog.base.enter_rule(_localctx.clone(), 124, RULE_annotationArg);
        let mut _localctx: Rc<AnnotationArgContextAll> = _localctx;
		let result: Result<(), ANTLRError> = (|| {

			//recog.base.enter_outer_alt(_localctx.clone(), 1);
			recog.base.enter_outer_alt(None, 1);
			{
			recog.base.set_state(930);
			recog.err_handler.sync(&mut recog.base)?;
			match  recog.interpreter.adaptive_predict(120,&mut recog.base)? {
				x if x == 1=>{
					{
					/*InvokeRule ident*/
					recog.base.set_state(927);
					let tmp = recog.ident()?;
					 cast_mut::<_,AnnotationArgContext >(&mut _localctx).name = Some(tmp.clone());
					  

					recog.base.set_state(928);
					recog.base.match_token(EQ,&mut recog.err_handler)?;

					}
				}

				_ => {}
			}
			/*InvokeRule expr*/
			recog.base.set_state(932);
			let tmp = recog.expr_rec(0)?;
			 cast_mut::<_,AnnotationArgContext >(&mut _localctx).value = Some(tmp.clone());
			  

			}
			Ok(())
		})();
		match result {
		Ok(_)=>{},
        Err(e @ ANTLRError::FallThrough(_)) => return Err(e),
		Err(ref re) => {
				//_localctx.exception = re;
				recog.err_handler.report_error(&mut recog.base, re);
				recog.err_handler.recover(&mut recog.base, re)?;
			}
		}
		recog.base.exit_rule();

		Ok(_localctx)
	}
}
//------------------- qualifiedTypeName ----------------
pub type QualifiedTypeNameContextAll<'input> = QualifiedTypeNameContext<'input>;


pub type QualifiedTypeNameContext<'input> = BaseParserRuleContext<'input,QualifiedTypeNameContextExt<'input>>;

#[derive(Clone)]
pub struct QualifiedTypeNameContextExt<'input>{
	pub typeName: Option<Rc<FullNameContextAll<'input>>>,
	pub typeParams: Option<Rc<GenericsContextAll<'input>>>,
ph:PhantomData<&'input str>
}

impl<'input> LibSLParserContext<'input> for QualifiedTypeNameContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for QualifiedTypeNameContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_qualifiedTypeName(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_qualifiedTypeName(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for QualifiedTypeNameContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_qualifiedTypeName }
	//fn type_rule_index() -> usize where Self: Sized { RULE_qualifiedTypeName }
}
antlr_rust::tid!{QualifiedTypeNameContextExt<'a>}

impl<'input> QualifiedTypeNameContextExt<'input>{
	fn new(parent: Option<Rc<dyn LibSLParserContext<'input> + 'input > >, invoking_state: isize) -> Rc<QualifiedTypeNameContextAll<'input>> {
		Rc::new(
			BaseParserRuleContext::new_parser_ctx(parent, invoking_state,QualifiedTypeNameContextExt{
				typeName: None, typeParams: None, 
				ph:PhantomData
			}),
		)
	}
}

pub trait QualifiedTypeNameContextAttrs<'input>: LibSLParserContext<'input> + BorrowMut<QualifiedTypeNameContextExt<'input>>{

fn fullName(&self) -> Option<Rc<FullNameContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}
fn generics(&self) -> Option<Rc<GenericsContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}

}

impl<'input> QualifiedTypeNameContextAttrs<'input> for QualifiedTypeNameContext<'input>{}

impl<'input, I, H> LibSLParser<'input, I, H>
where
    I: TokenStream<'input, TF = LocalTokenFactory<'input> > + TidAble<'input>,
    H: ErrorStrategy<'input,BaseParserType<'input,I>>
{
	pub fn qualifiedTypeName(&mut self,)
	-> Result<Rc<QualifiedTypeNameContextAll<'input>>,ANTLRError> {
		let mut recog = self;
		let _parentctx = recog.ctx.take();
		let mut _localctx = QualifiedTypeNameContextExt::new(_parentctx.clone(), recog.base.get_state());
        recog.base.enter_rule(_localctx.clone(), 126, RULE_qualifiedTypeName);
        let mut _localctx: Rc<QualifiedTypeNameContextAll> = _localctx;
		let mut _la: isize = -1;
		let result: Result<(), ANTLRError> = (|| {

			//recog.base.enter_outer_alt(_localctx.clone(), 1);
			recog.base.enter_outer_alt(None, 1);
			{
			/*InvokeRule fullName*/
			recog.base.set_state(934);
			let tmp = recog.fullName()?;
			 cast_mut::<_,QualifiedTypeNameContext >(&mut _localctx).typeName = Some(tmp.clone());
			  

			recog.base.set_state(936);
			recog.err_handler.sync(&mut recog.base)?;
			_la = recog.base.input.la(1);
			if _la==L_ANGLE {
				{
				/*InvokeRule generics*/
				recog.base.set_state(935);
				let tmp = recog.generics()?;
				 cast_mut::<_,QualifiedTypeNameContext >(&mut _localctx).typeParams = Some(tmp.clone());
				  

				}
			}

			}
			Ok(())
		})();
		match result {
		Ok(_)=>{},
        Err(e @ ANTLRError::FallThrough(_)) => return Err(e),
		Err(ref re) => {
				//_localctx.exception = re;
				recog.err_handler.report_error(&mut recog.base, re);
				recog.err_handler.recover(&mut recog.base, re)?;
			}
		}
		recog.base.exit_rule();

		Ok(_localctx)
	}
}
//------------------- fullName ----------------
pub type FullNameContextAll<'input> = FullNameContext<'input>;


pub type FullNameContext<'input> = BaseParserRuleContext<'input,FullNameContextExt<'input>>;

#[derive(Clone)]
pub struct FullNameContextExt<'input>{
	pub ident: Option<Rc<IdentContextAll<'input>>>,
	pub components:Vec<Rc<IdentContextAll<'input>>>,
ph:PhantomData<&'input str>
}

impl<'input> LibSLParserContext<'input> for FullNameContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for FullNameContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_fullName(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_fullName(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for FullNameContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_fullName }
	//fn type_rule_index() -> usize where Self: Sized { RULE_fullName }
}
antlr_rust::tid!{FullNameContextExt<'a>}

impl<'input> FullNameContextExt<'input>{
	fn new(parent: Option<Rc<dyn LibSLParserContext<'input> + 'input > >, invoking_state: isize) -> Rc<FullNameContextAll<'input>> {
		Rc::new(
			BaseParserRuleContext::new_parser_ctx(parent, invoking_state,FullNameContextExt{
				ident: None, 
				components: Vec::new(), 
				ph:PhantomData
			}),
		)
	}
}

pub trait FullNameContextAttrs<'input>: LibSLParserContext<'input> + BorrowMut<FullNameContextExt<'input>>{

fn ident_all(&self) ->  Vec<Rc<IdentContextAll<'input>>> where Self:Sized{
	self.children_of_type()
}
fn ident(&self, i: usize) -> Option<Rc<IdentContextAll<'input>>> where Self:Sized{
	self.child_of_type(i)
}
/// Retrieves all `TerminalNode`s corresponding to token DOT in current rule
fn DOT_all(&self) -> Vec<Rc<TerminalNode<'input,LibSLParserContextType>>>  where Self:Sized{
	self.get_tokens(DOT)
}
/// Retrieves 'i's TerminalNode corresponding to token DOT, starting from 0.
/// Returns `None` if number of children corresponding to token DOT is less or equal than `i`.
fn DOT(&self, i: usize) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(DOT, i)
}

}

impl<'input> FullNameContextAttrs<'input> for FullNameContext<'input>{}

impl<'input, I, H> LibSLParser<'input, I, H>
where
    I: TokenStream<'input, TF = LocalTokenFactory<'input> > + TidAble<'input>,
    H: ErrorStrategy<'input,BaseParserType<'input,I>>
{
	pub fn fullName(&mut self,)
	-> Result<Rc<FullNameContextAll<'input>>,ANTLRError> {
		let mut recog = self;
		let _parentctx = recog.ctx.take();
		let mut _localctx = FullNameContextExt::new(_parentctx.clone(), recog.base.get_state());
        recog.base.enter_rule(_localctx.clone(), 128, RULE_fullName);
        let mut _localctx: Rc<FullNameContextAll> = _localctx;
		let result: Result<(), ANTLRError> = (|| {

			let mut _alt: isize;
			//recog.base.enter_outer_alt(_localctx.clone(), 1);
			recog.base.enter_outer_alt(None, 1);
			{
			/*InvokeRule ident*/
			recog.base.set_state(938);
			let tmp = recog.ident()?;
			 cast_mut::<_,FullNameContext >(&mut _localctx).ident = Some(tmp.clone());
			  

			let temp =  cast_mut::<_,FullNameContext >(&mut _localctx).ident.clone().unwrap()
			 ;
			 cast_mut::<_,FullNameContext >(&mut _localctx).components.push(temp);
			  
			recog.base.set_state(943);
			recog.err_handler.sync(&mut recog.base)?;
			_alt = recog.interpreter.adaptive_predict(122,&mut recog.base)?;
			while { _alt!=2 && _alt!=INVALID_ALT } {
				if _alt==1 {
					{
					{
					recog.base.set_state(939);
					recog.base.match_token(DOT,&mut recog.err_handler)?;

					/*InvokeRule ident*/
					recog.base.set_state(940);
					let tmp = recog.ident()?;
					 cast_mut::<_,FullNameContext >(&mut _localctx).ident = Some(tmp.clone());
					  

					let temp =  cast_mut::<_,FullNameContext >(&mut _localctx).ident.clone().unwrap()
					 ;
					 cast_mut::<_,FullNameContext >(&mut _localctx).components.push(temp);
					  
					}
					} 
				}
				recog.base.set_state(945);
				recog.err_handler.sync(&mut recog.base)?;
				_alt = recog.interpreter.adaptive_predict(122,&mut recog.base)?;
			}
			}
			Ok(())
		})();
		match result {
		Ok(_)=>{},
        Err(e @ ANTLRError::FallThrough(_)) => return Err(e),
		Err(ref re) => {
				//_localctx.exception = re;
				recog.err_handler.report_error(&mut recog.base, re);
				recog.err_handler.recover(&mut recog.base, re)?;
			}
		}
		recog.base.exit_rule();

		Ok(_localctx)
	}
}
//------------------- whereClause ----------------
pub type WhereClauseContextAll<'input> = WhereClauseContext<'input>;


pub type WhereClauseContext<'input> = BaseParserRuleContext<'input,WhereClauseContextExt<'input>>;

#[derive(Clone)]
pub struct WhereClauseContextExt<'input>{
	pub typeConstraint: Option<Rc<TypeConstraintContextAll<'input>>>,
	pub constraints:Vec<Rc<TypeConstraintContextAll<'input>>>,
ph:PhantomData<&'input str>
}

impl<'input> LibSLParserContext<'input> for WhereClauseContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for WhereClauseContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_whereClause(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_whereClause(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for WhereClauseContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_whereClause }
	//fn type_rule_index() -> usize where Self: Sized { RULE_whereClause }
}
antlr_rust::tid!{WhereClauseContextExt<'a>}

impl<'input> WhereClauseContextExt<'input>{
	fn new(parent: Option<Rc<dyn LibSLParserContext<'input> + 'input > >, invoking_state: isize) -> Rc<WhereClauseContextAll<'input>> {
		Rc::new(
			BaseParserRuleContext::new_parser_ctx(parent, invoking_state,WhereClauseContextExt{
				typeConstraint: None, 
				constraints: Vec::new(), 
				ph:PhantomData
			}),
		)
	}
}

pub trait WhereClauseContextAttrs<'input>: LibSLParserContext<'input> + BorrowMut<WhereClauseContextExt<'input>>{

/// Retrieves first TerminalNode corresponding to token WHERE
/// Returns `None` if there is no child corresponding to token WHERE
fn WHERE(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(WHERE, 0)
}
fn typeConstraint_all(&self) ->  Vec<Rc<TypeConstraintContextAll<'input>>> where Self:Sized{
	self.children_of_type()
}
fn typeConstraint(&self, i: usize) -> Option<Rc<TypeConstraintContextAll<'input>>> where Self:Sized{
	self.child_of_type(i)
}
/// Retrieves all `TerminalNode`s corresponding to token COMMA in current rule
fn COMMA_all(&self) -> Vec<Rc<TerminalNode<'input,LibSLParserContextType>>>  where Self:Sized{
	self.get_tokens(COMMA)
}
/// Retrieves 'i's TerminalNode corresponding to token COMMA, starting from 0.
/// Returns `None` if number of children corresponding to token COMMA is less or equal than `i`.
fn COMMA(&self, i: usize) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(COMMA, i)
}

}

impl<'input> WhereClauseContextAttrs<'input> for WhereClauseContext<'input>{}

impl<'input, I, H> LibSLParser<'input, I, H>
where
    I: TokenStream<'input, TF = LocalTokenFactory<'input> > + TidAble<'input>,
    H: ErrorStrategy<'input,BaseParserType<'input,I>>
{
	pub fn whereClause(&mut self,)
	-> Result<Rc<WhereClauseContextAll<'input>>,ANTLRError> {
		let mut recog = self;
		let _parentctx = recog.ctx.take();
		let mut _localctx = WhereClauseContextExt::new(_parentctx.clone(), recog.base.get_state());
        recog.base.enter_rule(_localctx.clone(), 130, RULE_whereClause);
        let mut _localctx: Rc<WhereClauseContextAll> = _localctx;
		let mut _la: isize = -1;
		let result: Result<(), ANTLRError> = (|| {

			let mut _alt: isize;
			//recog.base.enter_outer_alt(_localctx.clone(), 1);
			recog.base.enter_outer_alt(None, 1);
			{
			recog.base.set_state(946);
			recog.base.match_token(WHERE,&mut recog.err_handler)?;

			/*InvokeRule typeConstraint*/
			recog.base.set_state(947);
			let tmp = recog.typeConstraint()?;
			 cast_mut::<_,WhereClauseContext >(&mut _localctx).typeConstraint = Some(tmp.clone());
			  

			let temp =  cast_mut::<_,WhereClauseContext >(&mut _localctx).typeConstraint.clone().unwrap()
			 ;
			 cast_mut::<_,WhereClauseContext >(&mut _localctx).constraints.push(temp);
			  
			recog.base.set_state(952);
			recog.err_handler.sync(&mut recog.base)?;
			_alt = recog.interpreter.adaptive_predict(123,&mut recog.base)?;
			while { _alt!=2 && _alt!=INVALID_ALT } {
				if _alt==1 {
					{
					{
					recog.base.set_state(948);
					recog.base.match_token(COMMA,&mut recog.err_handler)?;

					/*InvokeRule typeConstraint*/
					recog.base.set_state(949);
					let tmp = recog.typeConstraint()?;
					 cast_mut::<_,WhereClauseContext >(&mut _localctx).typeConstraint = Some(tmp.clone());
					  

					let temp =  cast_mut::<_,WhereClauseContext >(&mut _localctx).typeConstraint.clone().unwrap()
					 ;
					 cast_mut::<_,WhereClauseContext >(&mut _localctx).constraints.push(temp);
					  
					}
					} 
				}
				recog.base.set_state(954);
				recog.err_handler.sync(&mut recog.base)?;
				_alt = recog.interpreter.adaptive_predict(123,&mut recog.base)?;
			}
			recog.base.set_state(956);
			recog.err_handler.sync(&mut recog.base)?;
			_la = recog.base.input.la(1);
			if _la==COMMA {
				{
				recog.base.set_state(955);
				recog.base.match_token(COMMA,&mut recog.err_handler)?;

				}
			}

			}
			Ok(())
		})();
		match result {
		Ok(_)=>{},
        Err(e @ ANTLRError::FallThrough(_)) => return Err(e),
		Err(ref re) => {
				//_localctx.exception = re;
				recog.err_handler.report_error(&mut recog.base, re);
				recog.err_handler.recover(&mut recog.base, re)?;
			}
		}
		recog.base.exit_rule();

		Ok(_localctx)
	}
}
//------------------- typeConstraint ----------------
pub type TypeConstraintContextAll<'input> = TypeConstraintContext<'input>;


pub type TypeConstraintContext<'input> = BaseParserRuleContext<'input,TypeConstraintContextExt<'input>>;

#[derive(Clone)]
pub struct TypeConstraintContextExt<'input>{
	pub param: Option<Rc<IdentContextAll<'input>>>,
	pub bound: Option<Rc<TypeExprContextAll<'input>>>,
ph:PhantomData<&'input str>
}

impl<'input> LibSLParserContext<'input> for TypeConstraintContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for TypeConstraintContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_typeConstraint(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_typeConstraint(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for TypeConstraintContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_typeConstraint }
	//fn type_rule_index() -> usize where Self: Sized { RULE_typeConstraint }
}
antlr_rust::tid!{TypeConstraintContextExt<'a>}

impl<'input> TypeConstraintContextExt<'input>{
	fn new(parent: Option<Rc<dyn LibSLParserContext<'input> + 'input > >, invoking_state: isize) -> Rc<TypeConstraintContextAll<'input>> {
		Rc::new(
			BaseParserRuleContext::new_parser_ctx(parent, invoking_state,TypeConstraintContextExt{
				param: None, bound: None, 
				ph:PhantomData
			}),
		)
	}
}

pub trait TypeConstraintContextAttrs<'input>: LibSLParserContext<'input> + BorrowMut<TypeConstraintContextExt<'input>>{

/// Retrieves first TerminalNode corresponding to token COLON
/// Returns `None` if there is no child corresponding to token COLON
fn COLON(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(COLON, 0)
}
fn ident(&self) -> Option<Rc<IdentContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}
fn typeExpr(&self) -> Option<Rc<TypeExprContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}

}

impl<'input> TypeConstraintContextAttrs<'input> for TypeConstraintContext<'input>{}

impl<'input, I, H> LibSLParser<'input, I, H>
where
    I: TokenStream<'input, TF = LocalTokenFactory<'input> > + TidAble<'input>,
    H: ErrorStrategy<'input,BaseParserType<'input,I>>
{
	pub fn typeConstraint(&mut self,)
	-> Result<Rc<TypeConstraintContextAll<'input>>,ANTLRError> {
		let mut recog = self;
		let _parentctx = recog.ctx.take();
		let mut _localctx = TypeConstraintContextExt::new(_parentctx.clone(), recog.base.get_state());
        recog.base.enter_rule(_localctx.clone(), 132, RULE_typeConstraint);
        let mut _localctx: Rc<TypeConstraintContextAll> = _localctx;
		let result: Result<(), ANTLRError> = (|| {

			//recog.base.enter_outer_alt(_localctx.clone(), 1);
			recog.base.enter_outer_alt(None, 1);
			{
			/*InvokeRule ident*/
			recog.base.set_state(958);
			let tmp = recog.ident()?;
			 cast_mut::<_,TypeConstraintContext >(&mut _localctx).param = Some(tmp.clone());
			  

			recog.base.set_state(959);
			recog.base.match_token(COLON,&mut recog.err_handler)?;

			/*InvokeRule typeExpr*/
			recog.base.set_state(960);
			let tmp = recog.typeExpr_rec(0)?;
			 cast_mut::<_,TypeConstraintContext >(&mut _localctx).bound = Some(tmp.clone());
			  

			}
			Ok(())
		})();
		match result {
		Ok(_)=>{},
        Err(e @ ANTLRError::FallThrough(_)) => return Err(e),
		Err(ref re) => {
				//_localctx.exception = re;
				recog.err_handler.report_error(&mut recog.base, re);
				recog.err_handler.recover(&mut recog.base, re)?;
			}
		}
		recog.base.exit_rule();

		Ok(_localctx)
	}
}
//------------------- generics ----------------
pub type GenericsContextAll<'input> = GenericsContext<'input>;


pub type GenericsContext<'input> = BaseParserRuleContext<'input,GenericsContextExt<'input>>;

#[derive(Clone)]
pub struct GenericsContextExt<'input>{
	pub list: Option<Rc<GenericListContextAll<'input>>>,
ph:PhantomData<&'input str>
}

impl<'input> LibSLParserContext<'input> for GenericsContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for GenericsContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_generics(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_generics(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for GenericsContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_generics }
	//fn type_rule_index() -> usize where Self: Sized { RULE_generics }
}
antlr_rust::tid!{GenericsContextExt<'a>}

impl<'input> GenericsContextExt<'input>{
	fn new(parent: Option<Rc<dyn LibSLParserContext<'input> + 'input > >, invoking_state: isize) -> Rc<GenericsContextAll<'input>> {
		Rc::new(
			BaseParserRuleContext::new_parser_ctx(parent, invoking_state,GenericsContextExt{
				list: None, 
				ph:PhantomData
			}),
		)
	}
}

pub trait GenericsContextAttrs<'input>: LibSLParserContext<'input> + BorrowMut<GenericsContextExt<'input>>{

/// Retrieves first TerminalNode corresponding to token L_ANGLE
/// Returns `None` if there is no child corresponding to token L_ANGLE
fn L_ANGLE(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(L_ANGLE, 0)
}
/// Retrieves first TerminalNode corresponding to token R_ANGLE
/// Returns `None` if there is no child corresponding to token R_ANGLE
fn R_ANGLE(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(R_ANGLE, 0)
}
fn genericList(&self) -> Option<Rc<GenericListContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}
/// Retrieves first TerminalNode corresponding to token COMMA
/// Returns `None` if there is no child corresponding to token COMMA
fn COMMA(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(COMMA, 0)
}

}

impl<'input> GenericsContextAttrs<'input> for GenericsContext<'input>{}

impl<'input, I, H> LibSLParser<'input, I, H>
where
    I: TokenStream<'input, TF = LocalTokenFactory<'input> > + TidAble<'input>,
    H: ErrorStrategy<'input,BaseParserType<'input,I>>
{
	pub fn generics(&mut self,)
	-> Result<Rc<GenericsContextAll<'input>>,ANTLRError> {
		let mut recog = self;
		let _parentctx = recog.ctx.take();
		let mut _localctx = GenericsContextExt::new(_parentctx.clone(), recog.base.get_state());
        recog.base.enter_rule(_localctx.clone(), 134, RULE_generics);
        let mut _localctx: Rc<GenericsContextAll> = _localctx;
		let mut _la: isize = -1;
		let result: Result<(), ANTLRError> = (|| {

			//recog.base.enter_outer_alt(_localctx.clone(), 1);
			recog.base.enter_outer_alt(None, 1);
			{
			recog.base.set_state(962);
			recog.base.match_token(L_ANGLE,&mut recog.err_handler)?;

			recog.base.set_state(967);
			recog.err_handler.sync(&mut recog.base)?;
			_la = recog.base.input.la(1);
			if ((((_la - 82)) & !0x3f) == 0 && ((1usize << (_la - 82)) & 8307) != 0) {
				{
				/*InvokeRule genericList*/
				recog.base.set_state(963);
				let tmp = recog.genericList()?;
				 cast_mut::<_,GenericsContext >(&mut _localctx).list = Some(tmp.clone());
				  

				recog.base.set_state(965);
				recog.err_handler.sync(&mut recog.base)?;
				_la = recog.base.input.la(1);
				if _la==COMMA {
					{
					recog.base.set_state(964);
					recog.base.match_token(COMMA,&mut recog.err_handler)?;

					}
				}

				}
			}

			recog.base.set_state(969);
			recog.base.match_token(R_ANGLE,&mut recog.err_handler)?;

			}
			Ok(())
		})();
		match result {
		Ok(_)=>{},
        Err(e @ ANTLRError::FallThrough(_)) => return Err(e),
		Err(ref re) => {
				//_localctx.exception = re;
				recog.err_handler.report_error(&mut recog.base, re);
				recog.err_handler.recover(&mut recog.base, re)?;
			}
		}
		recog.base.exit_rule();

		Ok(_localctx)
	}
}
//------------------- genericList ----------------
pub type GenericListContextAll<'input> = GenericListContext<'input>;


pub type GenericListContext<'input> = BaseParserRuleContext<'input,GenericListContextExt<'input>>;

#[derive(Clone)]
pub struct GenericListContextExt<'input>{
	pub generic: Option<Rc<GenericContextAll<'input>>>,
	pub params:Vec<Rc<GenericContextAll<'input>>>,
ph:PhantomData<&'input str>
}

impl<'input> LibSLParserContext<'input> for GenericListContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for GenericListContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_genericList(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_genericList(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for GenericListContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_genericList }
	//fn type_rule_index() -> usize where Self: Sized { RULE_genericList }
}
antlr_rust::tid!{GenericListContextExt<'a>}

impl<'input> GenericListContextExt<'input>{
	fn new(parent: Option<Rc<dyn LibSLParserContext<'input> + 'input > >, invoking_state: isize) -> Rc<GenericListContextAll<'input>> {
		Rc::new(
			BaseParserRuleContext::new_parser_ctx(parent, invoking_state,GenericListContextExt{
				generic: None, 
				params: Vec::new(), 
				ph:PhantomData
			}),
		)
	}
}

pub trait GenericListContextAttrs<'input>: LibSLParserContext<'input> + BorrowMut<GenericListContextExt<'input>>{

fn generic_all(&self) ->  Vec<Rc<GenericContextAll<'input>>> where Self:Sized{
	self.children_of_type()
}
fn generic(&self, i: usize) -> Option<Rc<GenericContextAll<'input>>> where Self:Sized{
	self.child_of_type(i)
}
/// Retrieves all `TerminalNode`s corresponding to token COMMA in current rule
fn COMMA_all(&self) -> Vec<Rc<TerminalNode<'input,LibSLParserContextType>>>  where Self:Sized{
	self.get_tokens(COMMA)
}
/// Retrieves 'i's TerminalNode corresponding to token COMMA, starting from 0.
/// Returns `None` if number of children corresponding to token COMMA is less or equal than `i`.
fn COMMA(&self, i: usize) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(COMMA, i)
}

}

impl<'input> GenericListContextAttrs<'input> for GenericListContext<'input>{}

impl<'input, I, H> LibSLParser<'input, I, H>
where
    I: TokenStream<'input, TF = LocalTokenFactory<'input> > + TidAble<'input>,
    H: ErrorStrategy<'input,BaseParserType<'input,I>>
{
	pub fn genericList(&mut self,)
	-> Result<Rc<GenericListContextAll<'input>>,ANTLRError> {
		let mut recog = self;
		let _parentctx = recog.ctx.take();
		let mut _localctx = GenericListContextExt::new(_parentctx.clone(), recog.base.get_state());
        recog.base.enter_rule(_localctx.clone(), 136, RULE_genericList);
        let mut _localctx: Rc<GenericListContextAll> = _localctx;
		let result: Result<(), ANTLRError> = (|| {

			let mut _alt: isize;
			//recog.base.enter_outer_alt(_localctx.clone(), 1);
			recog.base.enter_outer_alt(None, 1);
			{
			/*InvokeRule generic*/
			recog.base.set_state(971);
			let tmp = recog.generic()?;
			 cast_mut::<_,GenericListContext >(&mut _localctx).generic = Some(tmp.clone());
			  

			let temp =  cast_mut::<_,GenericListContext >(&mut _localctx).generic.clone().unwrap()
			 ;
			 cast_mut::<_,GenericListContext >(&mut _localctx).params.push(temp);
			  
			recog.base.set_state(976);
			recog.err_handler.sync(&mut recog.base)?;
			_alt = recog.interpreter.adaptive_predict(127,&mut recog.base)?;
			while { _alt!=2 && _alt!=INVALID_ALT } {
				if _alt==1 {
					{
					{
					recog.base.set_state(972);
					recog.base.match_token(COMMA,&mut recog.err_handler)?;

					/*InvokeRule generic*/
					recog.base.set_state(973);
					let tmp = recog.generic()?;
					 cast_mut::<_,GenericListContext >(&mut _localctx).generic = Some(tmp.clone());
					  

					let temp =  cast_mut::<_,GenericListContext >(&mut _localctx).generic.clone().unwrap()
					 ;
					 cast_mut::<_,GenericListContext >(&mut _localctx).params.push(temp);
					  
					}
					} 
				}
				recog.base.set_state(978);
				recog.err_handler.sync(&mut recog.base)?;
				_alt = recog.interpreter.adaptive_predict(127,&mut recog.base)?;
			}
			}
			Ok(())
		})();
		match result {
		Ok(_)=>{},
        Err(e @ ANTLRError::FallThrough(_)) => return Err(e),
		Err(ref re) => {
				//_localctx.exception = re;
				recog.err_handler.report_error(&mut recog.base, re);
				recog.err_handler.recover(&mut recog.base, re)?;
			}
		}
		recog.base.exit_rule();

		Ok(_localctx)
	}
}
//------------------- generic ----------------
pub type GenericContextAll<'input> = GenericContext<'input>;


pub type GenericContext<'input> = BaseParserRuleContext<'input,GenericContextExt<'input>>;

#[derive(Clone)]
pub struct GenericContextExt<'input>{
	pub variance: Option<Rc<VarianceSpecContextAll<'input>>>,
	pub name: Option<Rc<IdentContextAll<'input>>>,
ph:PhantomData<&'input str>
}

impl<'input> LibSLParserContext<'input> for GenericContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for GenericContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_generic(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_generic(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for GenericContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_generic }
	//fn type_rule_index() -> usize where Self: Sized { RULE_generic }
}
antlr_rust::tid!{GenericContextExt<'a>}

impl<'input> GenericContextExt<'input>{
	fn new(parent: Option<Rc<dyn LibSLParserContext<'input> + 'input > >, invoking_state: isize) -> Rc<GenericContextAll<'input>> {
		Rc::new(
			BaseParserRuleContext::new_parser_ctx(parent, invoking_state,GenericContextExt{
				variance: None, name: None, 
				ph:PhantomData
			}),
		)
	}
}

pub trait GenericContextAttrs<'input>: LibSLParserContext<'input> + BorrowMut<GenericContextExt<'input>>{

fn ident(&self) -> Option<Rc<IdentContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}
fn varianceSpec(&self) -> Option<Rc<VarianceSpecContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}

}

impl<'input> GenericContextAttrs<'input> for GenericContext<'input>{}

impl<'input, I, H> LibSLParser<'input, I, H>
where
    I: TokenStream<'input, TF = LocalTokenFactory<'input> > + TidAble<'input>,
    H: ErrorStrategy<'input,BaseParserType<'input,I>>
{
	pub fn generic(&mut self,)
	-> Result<Rc<GenericContextAll<'input>>,ANTLRError> {
		let mut recog = self;
		let _parentctx = recog.ctx.take();
		let mut _localctx = GenericContextExt::new(_parentctx.clone(), recog.base.get_state());
        recog.base.enter_rule(_localctx.clone(), 138, RULE_generic);
        let mut _localctx: Rc<GenericContextAll> = _localctx;
		let mut _la: isize = -1;
		let result: Result<(), ANTLRError> = (|| {

			//recog.base.enter_outer_alt(_localctx.clone(), 1);
			recog.base.enter_outer_alt(None, 1);
			{
			recog.base.set_state(980);
			recog.err_handler.sync(&mut recog.base)?;
			_la = recog.base.input.la(1);
			if _la==IN || _la==OUT {
				{
				/*InvokeRule varianceSpec*/
				recog.base.set_state(979);
				let tmp = recog.varianceSpec()?;
				 cast_mut::<_,GenericContext >(&mut _localctx).variance = Some(tmp.clone());
				  

				}
			}

			/*InvokeRule ident*/
			recog.base.set_state(982);
			let tmp = recog.ident()?;
			 cast_mut::<_,GenericContext >(&mut _localctx).name = Some(tmp.clone());
			  

			}
			Ok(())
		})();
		match result {
		Ok(_)=>{},
        Err(e @ ANTLRError::FallThrough(_)) => return Err(e),
		Err(ref re) => {
				//_localctx.exception = re;
				recog.err_handler.report_error(&mut recog.base, re);
				recog.err_handler.recover(&mut recog.base, re)?;
			}
		}
		recog.base.exit_rule();

		Ok(_localctx)
	}
}
//------------------- varianceSpec ----------------
#[derive(Debug)]
pub enum VarianceSpecContextAll<'input>{
	CovariantContext(CovariantContext<'input>),
	ContravariantContext(ContravariantContext<'input>),
	InvariantContext(InvariantContext<'input>),
Error(VarianceSpecContext<'input>)
}
antlr_rust::tid!{VarianceSpecContextAll<'a>}

impl<'input> antlr_rust::parser_rule_context::DerefSeal for VarianceSpecContextAll<'input>{}

impl<'input> LibSLParserContext<'input> for VarianceSpecContextAll<'input>{}

impl<'input> Deref for VarianceSpecContextAll<'input>{
	type Target = dyn VarianceSpecContextAttrs<'input> + 'input;
	fn deref(&self) -> &Self::Target{
		use VarianceSpecContextAll::*;
		match self{
			CovariantContext(inner) => inner,
			ContravariantContext(inner) => inner,
			InvariantContext(inner) => inner,
Error(inner) => inner
		}
	}
}
impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for VarianceSpecContextAll<'input>{
    fn enter(&self, listener: &mut (dyn LibSLParserListener<'input> + 'a)) { self.deref().enter(listener) }
    fn exit(&self, listener: &mut (dyn LibSLParserListener<'input> + 'a)) { self.deref().exit(listener) }
}



pub type VarianceSpecContext<'input> = BaseParserRuleContext<'input,VarianceSpecContextExt<'input>>;

#[derive(Clone)]
pub struct VarianceSpecContextExt<'input>{
ph:PhantomData<&'input str>
}

impl<'input> LibSLParserContext<'input> for VarianceSpecContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for VarianceSpecContext<'input>{
}

impl<'input> CustomRuleContext<'input> for VarianceSpecContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_varianceSpec }
	//fn type_rule_index() -> usize where Self: Sized { RULE_varianceSpec }
}
antlr_rust::tid!{VarianceSpecContextExt<'a>}

impl<'input> VarianceSpecContextExt<'input>{
	fn new(parent: Option<Rc<dyn LibSLParserContext<'input> + 'input > >, invoking_state: isize) -> Rc<VarianceSpecContextAll<'input>> {
		Rc::new(
		VarianceSpecContextAll::Error(
			BaseParserRuleContext::new_parser_ctx(parent, invoking_state,VarianceSpecContextExt{
				ph:PhantomData
			}),
		)
		)
	}
}

pub trait VarianceSpecContextAttrs<'input>: LibSLParserContext<'input> + BorrowMut<VarianceSpecContextExt<'input>>{


}

impl<'input> VarianceSpecContextAttrs<'input> for VarianceSpecContext<'input>{}

pub type CovariantContext<'input> = BaseParserRuleContext<'input,CovariantContextExt<'input>>;

pub trait CovariantContextAttrs<'input>: LibSLParserContext<'input>{
	/// Retrieves first TerminalNode corresponding to token OUT
	/// Returns `None` if there is no child corresponding to token OUT
	fn OUT(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(OUT, 0)
	}
}

impl<'input> CovariantContextAttrs<'input> for CovariantContext<'input>{}

pub struct CovariantContextExt<'input>{
	__base:VarianceSpecContextExt<'input>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{CovariantContextExt<'a>}

impl<'input> LibSLParserContext<'input> for CovariantContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for CovariantContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_Covariant(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_Covariant(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for CovariantContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_varianceSpec }
	//fn type_rule_index() -> usize where Self: Sized { RULE_varianceSpec }
}

impl<'input> Borrow<VarianceSpecContextExt<'input>> for CovariantContext<'input>{
	fn borrow(&self) -> &VarianceSpecContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<VarianceSpecContextExt<'input>> for CovariantContext<'input>{
	fn borrow_mut(&mut self) -> &mut VarianceSpecContextExt<'input> { &mut self.__base }
}

impl<'input> VarianceSpecContextAttrs<'input> for CovariantContext<'input> {}

impl<'input> CovariantContextExt<'input>{
	fn new(ctx: &dyn VarianceSpecContextAttrs<'input>) -> Rc<VarianceSpecContextAll<'input>>  {
		Rc::new(
			VarianceSpecContextAll::CovariantContext(
				BaseParserRuleContext::copy_from(ctx,CovariantContextExt{
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type ContravariantContext<'input> = BaseParserRuleContext<'input,ContravariantContextExt<'input>>;

pub trait ContravariantContextAttrs<'input>: LibSLParserContext<'input>{
	/// Retrieves first TerminalNode corresponding to token IN
	/// Returns `None` if there is no child corresponding to token IN
	fn IN(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(IN, 0)
	}
}

impl<'input> ContravariantContextAttrs<'input> for ContravariantContext<'input>{}

pub struct ContravariantContextExt<'input>{
	__base:VarianceSpecContextExt<'input>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{ContravariantContextExt<'a>}

impl<'input> LibSLParserContext<'input> for ContravariantContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for ContravariantContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_Contravariant(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_Contravariant(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for ContravariantContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_varianceSpec }
	//fn type_rule_index() -> usize where Self: Sized { RULE_varianceSpec }
}

impl<'input> Borrow<VarianceSpecContextExt<'input>> for ContravariantContext<'input>{
	fn borrow(&self) -> &VarianceSpecContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<VarianceSpecContextExt<'input>> for ContravariantContext<'input>{
	fn borrow_mut(&mut self) -> &mut VarianceSpecContextExt<'input> { &mut self.__base }
}

impl<'input> VarianceSpecContextAttrs<'input> for ContravariantContext<'input> {}

impl<'input> ContravariantContextExt<'input>{
	fn new(ctx: &dyn VarianceSpecContextAttrs<'input>) -> Rc<VarianceSpecContextAll<'input>>  {
		Rc::new(
			VarianceSpecContextAll::ContravariantContext(
				BaseParserRuleContext::copy_from(ctx,ContravariantContextExt{
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type InvariantContext<'input> = BaseParserRuleContext<'input,InvariantContextExt<'input>>;

pub trait InvariantContextAttrs<'input>: LibSLParserContext<'input>{
	/// Retrieves first TerminalNode corresponding to token IN
	/// Returns `None` if there is no child corresponding to token IN
	fn IN(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(IN, 0)
	}
	/// Retrieves first TerminalNode corresponding to token OUT
	/// Returns `None` if there is no child corresponding to token OUT
	fn OUT(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(OUT, 0)
	}
}

impl<'input> InvariantContextAttrs<'input> for InvariantContext<'input>{}

pub struct InvariantContextExt<'input>{
	__base:VarianceSpecContextExt<'input>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{InvariantContextExt<'a>}

impl<'input> LibSLParserContext<'input> for InvariantContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for InvariantContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_Invariant(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_Invariant(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for InvariantContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_varianceSpec }
	//fn type_rule_index() -> usize where Self: Sized { RULE_varianceSpec }
}

impl<'input> Borrow<VarianceSpecContextExt<'input>> for InvariantContext<'input>{
	fn borrow(&self) -> &VarianceSpecContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<VarianceSpecContextExt<'input>> for InvariantContext<'input>{
	fn borrow_mut(&mut self) -> &mut VarianceSpecContextExt<'input> { &mut self.__base }
}

impl<'input> VarianceSpecContextAttrs<'input> for InvariantContext<'input> {}

impl<'input> InvariantContextExt<'input>{
	fn new(ctx: &dyn VarianceSpecContextAttrs<'input>) -> Rc<VarianceSpecContextAll<'input>>  {
		Rc::new(
			VarianceSpecContextAll::InvariantContext(
				BaseParserRuleContext::copy_from(ctx,InvariantContextExt{
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

impl<'input, I, H> LibSLParser<'input, I, H>
where
    I: TokenStream<'input, TF = LocalTokenFactory<'input> > + TidAble<'input>,
    H: ErrorStrategy<'input,BaseParserType<'input,I>>
{
	pub fn varianceSpec(&mut self,)
	-> Result<Rc<VarianceSpecContextAll<'input>>,ANTLRError> {
		let mut recog = self;
		let _parentctx = recog.ctx.take();
		let mut _localctx = VarianceSpecContextExt::new(_parentctx.clone(), recog.base.get_state());
        recog.base.enter_rule(_localctx.clone(), 140, RULE_varianceSpec);
        let mut _localctx: Rc<VarianceSpecContextAll> = _localctx;
		let result: Result<(), ANTLRError> = (|| {

			recog.base.set_state(988);
			recog.err_handler.sync(&mut recog.base)?;
			match  recog.interpreter.adaptive_predict(129,&mut recog.base)? {
				1 =>{
					let tmp = CovariantContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 1);
					_localctx = tmp;
					{
					recog.base.set_state(984);
					recog.base.match_token(OUT,&mut recog.err_handler)?;

					}
				}
			,
				2 =>{
					let tmp = ContravariantContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 2);
					_localctx = tmp;
					{
					recog.base.set_state(985);
					recog.base.match_token(IN,&mut recog.err_handler)?;

					}
				}
			,
				3 =>{
					let tmp = InvariantContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 3);
					_localctx = tmp;
					{
					recog.base.set_state(986);
					recog.base.match_token(IN,&mut recog.err_handler)?;

					recog.base.set_state(987);
					recog.base.match_token(OUT,&mut recog.err_handler)?;

					}
				}

				_ => {}
			}
			Ok(())
		})();
		match result {
		Ok(_)=>{},
        Err(e @ ANTLRError::FallThrough(_)) => return Err(e),
		Err(ref re) => {
				//_localctx.exception = re;
				recog.err_handler.report_error(&mut recog.base, re);
				recog.err_handler.recover(&mut recog.base, re)?;
			}
		}
		recog.base.exit_rule();

		Ok(_localctx)
	}
}
//------------------- typeExprList ----------------
pub type TypeExprListContextAll<'input> = TypeExprListContext<'input>;


pub type TypeExprListContext<'input> = BaseParserRuleContext<'input,TypeExprListContextExt<'input>>;

#[derive(Clone)]
pub struct TypeExprListContextExt<'input>{
	pub typeExpr: Option<Rc<TypeExprContextAll<'input>>>,
	pub typeExprs:Vec<Rc<TypeExprContextAll<'input>>>,
ph:PhantomData<&'input str>
}

impl<'input> LibSLParserContext<'input> for TypeExprListContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for TypeExprListContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_typeExprList(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_typeExprList(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for TypeExprListContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_typeExprList }
	//fn type_rule_index() -> usize where Self: Sized { RULE_typeExprList }
}
antlr_rust::tid!{TypeExprListContextExt<'a>}

impl<'input> TypeExprListContextExt<'input>{
	fn new(parent: Option<Rc<dyn LibSLParserContext<'input> + 'input > >, invoking_state: isize) -> Rc<TypeExprListContextAll<'input>> {
		Rc::new(
			BaseParserRuleContext::new_parser_ctx(parent, invoking_state,TypeExprListContextExt{
				typeExpr: None, 
				typeExprs: Vec::new(), 
				ph:PhantomData
			}),
		)
	}
}

pub trait TypeExprListContextAttrs<'input>: LibSLParserContext<'input> + BorrowMut<TypeExprListContextExt<'input>>{

fn typeExpr_all(&self) ->  Vec<Rc<TypeExprContextAll<'input>>> where Self:Sized{
	self.children_of_type()
}
fn typeExpr(&self, i: usize) -> Option<Rc<TypeExprContextAll<'input>>> where Self:Sized{
	self.child_of_type(i)
}
/// Retrieves all `TerminalNode`s corresponding to token COMMA in current rule
fn COMMA_all(&self) -> Vec<Rc<TerminalNode<'input,LibSLParserContextType>>>  where Self:Sized{
	self.get_tokens(COMMA)
}
/// Retrieves 'i's TerminalNode corresponding to token COMMA, starting from 0.
/// Returns `None` if number of children corresponding to token COMMA is less or equal than `i`.
fn COMMA(&self, i: usize) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(COMMA, i)
}

}

impl<'input> TypeExprListContextAttrs<'input> for TypeExprListContext<'input>{}

impl<'input, I, H> LibSLParser<'input, I, H>
where
    I: TokenStream<'input, TF = LocalTokenFactory<'input> > + TidAble<'input>,
    H: ErrorStrategy<'input,BaseParserType<'input,I>>
{
	pub fn typeExprList(&mut self,)
	-> Result<Rc<TypeExprListContextAll<'input>>,ANTLRError> {
		let mut recog = self;
		let _parentctx = recog.ctx.take();
		let mut _localctx = TypeExprListContextExt::new(_parentctx.clone(), recog.base.get_state());
        recog.base.enter_rule(_localctx.clone(), 142, RULE_typeExprList);
        let mut _localctx: Rc<TypeExprListContextAll> = _localctx;
		let result: Result<(), ANTLRError> = (|| {

			let mut _alt: isize;
			//recog.base.enter_outer_alt(_localctx.clone(), 1);
			recog.base.enter_outer_alt(None, 1);
			{
			/*InvokeRule typeExpr*/
			recog.base.set_state(990);
			let tmp = recog.typeExpr_rec(0)?;
			 cast_mut::<_,TypeExprListContext >(&mut _localctx).typeExpr = Some(tmp.clone());
			  

			let temp =  cast_mut::<_,TypeExprListContext >(&mut _localctx).typeExpr.clone().unwrap()
			 ;
			 cast_mut::<_,TypeExprListContext >(&mut _localctx).typeExprs.push(temp);
			  
			recog.base.set_state(995);
			recog.err_handler.sync(&mut recog.base)?;
			_alt = recog.interpreter.adaptive_predict(130,&mut recog.base)?;
			while { _alt!=2 && _alt!=INVALID_ALT } {
				if _alt==1 {
					{
					{
					recog.base.set_state(991);
					recog.base.match_token(COMMA,&mut recog.err_handler)?;

					/*InvokeRule typeExpr*/
					recog.base.set_state(992);
					let tmp = recog.typeExpr_rec(0)?;
					 cast_mut::<_,TypeExprListContext >(&mut _localctx).typeExpr = Some(tmp.clone());
					  

					let temp =  cast_mut::<_,TypeExprListContext >(&mut _localctx).typeExpr.clone().unwrap()
					 ;
					 cast_mut::<_,TypeExprListContext >(&mut _localctx).typeExprs.push(temp);
					  
					}
					} 
				}
				recog.base.set_state(997);
				recog.err_handler.sync(&mut recog.base)?;
				_alt = recog.interpreter.adaptive_predict(130,&mut recog.base)?;
			}
			}
			Ok(())
		})();
		match result {
		Ok(_)=>{},
        Err(e @ ANTLRError::FallThrough(_)) => return Err(e),
		Err(ref re) => {
				//_localctx.exception = re;
				recog.err_handler.report_error(&mut recog.base, re);
				recog.err_handler.recover(&mut recog.base, re)?;
			}
		}
		recog.base.exit_rule();

		Ok(_localctx)
	}
}
//------------------- atomicTypeExpr ----------------
#[derive(Debug)]
pub enum AtomicTypeExprContextAll<'input>{
	TypeExprNameContext(TypeExprNameContext<'input>),
	TypeExprPrimitiveLitContext(TypeExprPrimitiveLitContext<'input>),
	TypeExprPointerContext(TypeExprPointerContext<'input>),
	TypeExprParenContext(TypeExprParenContext<'input>),
Error(AtomicTypeExprContext<'input>)
}
antlr_rust::tid!{AtomicTypeExprContextAll<'a>}

impl<'input> antlr_rust::parser_rule_context::DerefSeal for AtomicTypeExprContextAll<'input>{}

impl<'input> LibSLParserContext<'input> for AtomicTypeExprContextAll<'input>{}

impl<'input> Deref for AtomicTypeExprContextAll<'input>{
	type Target = dyn AtomicTypeExprContextAttrs<'input> + 'input;
	fn deref(&self) -> &Self::Target{
		use AtomicTypeExprContextAll::*;
		match self{
			TypeExprNameContext(inner) => inner,
			TypeExprPrimitiveLitContext(inner) => inner,
			TypeExprPointerContext(inner) => inner,
			TypeExprParenContext(inner) => inner,
Error(inner) => inner
		}
	}
}
impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for AtomicTypeExprContextAll<'input>{
    fn enter(&self, listener: &mut (dyn LibSLParserListener<'input> + 'a)) { self.deref().enter(listener) }
    fn exit(&self, listener: &mut (dyn LibSLParserListener<'input> + 'a)) { self.deref().exit(listener) }
}



pub type AtomicTypeExprContext<'input> = BaseParserRuleContext<'input,AtomicTypeExprContextExt<'input>>;

#[derive(Clone)]
pub struct AtomicTypeExprContextExt<'input>{
ph:PhantomData<&'input str>
}

impl<'input> LibSLParserContext<'input> for AtomicTypeExprContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for AtomicTypeExprContext<'input>{
}

impl<'input> CustomRuleContext<'input> for AtomicTypeExprContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_atomicTypeExpr }
	//fn type_rule_index() -> usize where Self: Sized { RULE_atomicTypeExpr }
}
antlr_rust::tid!{AtomicTypeExprContextExt<'a>}

impl<'input> AtomicTypeExprContextExt<'input>{
	fn new(parent: Option<Rc<dyn LibSLParserContext<'input> + 'input > >, invoking_state: isize) -> Rc<AtomicTypeExprContextAll<'input>> {
		Rc::new(
		AtomicTypeExprContextAll::Error(
			BaseParserRuleContext::new_parser_ctx(parent, invoking_state,AtomicTypeExprContextExt{
				ph:PhantomData
			}),
		)
		)
	}
}

pub trait AtomicTypeExprContextAttrs<'input>: LibSLParserContext<'input> + BorrowMut<AtomicTypeExprContextExt<'input>>{


}

impl<'input> AtomicTypeExprContextAttrs<'input> for AtomicTypeExprContext<'input>{}

pub type TypeExprNameContext<'input> = BaseParserRuleContext<'input,TypeExprNameContextExt<'input>>;

pub trait TypeExprNameContextAttrs<'input>: LibSLParserContext<'input>{
	fn nameTypeExpr(&self) -> Option<Rc<NameTypeExprContextAll<'input>>> where Self:Sized{
		self.child_of_type(0)
	}
}

impl<'input> TypeExprNameContextAttrs<'input> for TypeExprNameContext<'input>{}

pub struct TypeExprNameContextExt<'input>{
	__base:AtomicTypeExprContextExt<'input>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{TypeExprNameContextExt<'a>}

impl<'input> LibSLParserContext<'input> for TypeExprNameContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for TypeExprNameContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_TypeExprName(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_TypeExprName(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for TypeExprNameContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_atomicTypeExpr }
	//fn type_rule_index() -> usize where Self: Sized { RULE_atomicTypeExpr }
}

impl<'input> Borrow<AtomicTypeExprContextExt<'input>> for TypeExprNameContext<'input>{
	fn borrow(&self) -> &AtomicTypeExprContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<AtomicTypeExprContextExt<'input>> for TypeExprNameContext<'input>{
	fn borrow_mut(&mut self) -> &mut AtomicTypeExprContextExt<'input> { &mut self.__base }
}

impl<'input> AtomicTypeExprContextAttrs<'input> for TypeExprNameContext<'input> {}

impl<'input> TypeExprNameContextExt<'input>{
	fn new(ctx: &dyn AtomicTypeExprContextAttrs<'input>) -> Rc<AtomicTypeExprContextAll<'input>>  {
		Rc::new(
			AtomicTypeExprContextAll::TypeExprNameContext(
				BaseParserRuleContext::copy_from(ctx,TypeExprNameContextExt{
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type TypeExprPrimitiveLitContext<'input> = BaseParserRuleContext<'input,TypeExprPrimitiveLitContextExt<'input>>;

pub trait TypeExprPrimitiveLitContextAttrs<'input>: LibSLParserContext<'input>{
	fn primitiveLit(&self) -> Option<Rc<PrimitiveLitContextAll<'input>>> where Self:Sized{
		self.child_of_type(0)
	}
}

impl<'input> TypeExprPrimitiveLitContextAttrs<'input> for TypeExprPrimitiveLitContext<'input>{}

pub struct TypeExprPrimitiveLitContextExt<'input>{
	__base:AtomicTypeExprContextExt<'input>,
	pub lit: Option<Rc<PrimitiveLitContextAll<'input>>>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{TypeExprPrimitiveLitContextExt<'a>}

impl<'input> LibSLParserContext<'input> for TypeExprPrimitiveLitContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for TypeExprPrimitiveLitContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_TypeExprPrimitiveLit(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_TypeExprPrimitiveLit(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for TypeExprPrimitiveLitContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_atomicTypeExpr }
	//fn type_rule_index() -> usize where Self: Sized { RULE_atomicTypeExpr }
}

impl<'input> Borrow<AtomicTypeExprContextExt<'input>> for TypeExprPrimitiveLitContext<'input>{
	fn borrow(&self) -> &AtomicTypeExprContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<AtomicTypeExprContextExt<'input>> for TypeExprPrimitiveLitContext<'input>{
	fn borrow_mut(&mut self) -> &mut AtomicTypeExprContextExt<'input> { &mut self.__base }
}

impl<'input> AtomicTypeExprContextAttrs<'input> for TypeExprPrimitiveLitContext<'input> {}

impl<'input> TypeExprPrimitiveLitContextExt<'input>{
	fn new(ctx: &dyn AtomicTypeExprContextAttrs<'input>) -> Rc<AtomicTypeExprContextAll<'input>>  {
		Rc::new(
			AtomicTypeExprContextAll::TypeExprPrimitiveLitContext(
				BaseParserRuleContext::copy_from(ctx,TypeExprPrimitiveLitContextExt{
        			lit:None, 
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type TypeExprPointerContext<'input> = BaseParserRuleContext<'input,TypeExprPointerContextExt<'input>>;

pub trait TypeExprPointerContextAttrs<'input>: LibSLParserContext<'input>{
	fn pointerTypeExpr(&self) -> Option<Rc<PointerTypeExprContextAll<'input>>> where Self:Sized{
		self.child_of_type(0)
	}
}

impl<'input> TypeExprPointerContextAttrs<'input> for TypeExprPointerContext<'input>{}

pub struct TypeExprPointerContextExt<'input>{
	__base:AtomicTypeExprContextExt<'input>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{TypeExprPointerContextExt<'a>}

impl<'input> LibSLParserContext<'input> for TypeExprPointerContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for TypeExprPointerContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_TypeExprPointer(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_TypeExprPointer(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for TypeExprPointerContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_atomicTypeExpr }
	//fn type_rule_index() -> usize where Self: Sized { RULE_atomicTypeExpr }
}

impl<'input> Borrow<AtomicTypeExprContextExt<'input>> for TypeExprPointerContext<'input>{
	fn borrow(&self) -> &AtomicTypeExprContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<AtomicTypeExprContextExt<'input>> for TypeExprPointerContext<'input>{
	fn borrow_mut(&mut self) -> &mut AtomicTypeExprContextExt<'input> { &mut self.__base }
}

impl<'input> AtomicTypeExprContextAttrs<'input> for TypeExprPointerContext<'input> {}

impl<'input> TypeExprPointerContextExt<'input>{
	fn new(ctx: &dyn AtomicTypeExprContextAttrs<'input>) -> Rc<AtomicTypeExprContextAll<'input>>  {
		Rc::new(
			AtomicTypeExprContextAll::TypeExprPointerContext(
				BaseParserRuleContext::copy_from(ctx,TypeExprPointerContextExt{
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type TypeExprParenContext<'input> = BaseParserRuleContext<'input,TypeExprParenContextExt<'input>>;

pub trait TypeExprParenContextAttrs<'input>: LibSLParserContext<'input>{
	/// Retrieves first TerminalNode corresponding to token L_PAREN
	/// Returns `None` if there is no child corresponding to token L_PAREN
	fn L_PAREN(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(L_PAREN, 0)
	}
	/// Retrieves first TerminalNode corresponding to token R_PAREN
	/// Returns `None` if there is no child corresponding to token R_PAREN
	fn R_PAREN(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(R_PAREN, 0)
	}
	fn typeExpr(&self) -> Option<Rc<TypeExprContextAll<'input>>> where Self:Sized{
		self.child_of_type(0)
	}
}

impl<'input> TypeExprParenContextAttrs<'input> for TypeExprParenContext<'input>{}

pub struct TypeExprParenContextExt<'input>{
	__base:AtomicTypeExprContextExt<'input>,
	pub inner: Option<Rc<TypeExprContextAll<'input>>>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{TypeExprParenContextExt<'a>}

impl<'input> LibSLParserContext<'input> for TypeExprParenContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for TypeExprParenContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_TypeExprParen(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_TypeExprParen(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for TypeExprParenContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_atomicTypeExpr }
	//fn type_rule_index() -> usize where Self: Sized { RULE_atomicTypeExpr }
}

impl<'input> Borrow<AtomicTypeExprContextExt<'input>> for TypeExprParenContext<'input>{
	fn borrow(&self) -> &AtomicTypeExprContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<AtomicTypeExprContextExt<'input>> for TypeExprParenContext<'input>{
	fn borrow_mut(&mut self) -> &mut AtomicTypeExprContextExt<'input> { &mut self.__base }
}

impl<'input> AtomicTypeExprContextAttrs<'input> for TypeExprParenContext<'input> {}

impl<'input> TypeExprParenContextExt<'input>{
	fn new(ctx: &dyn AtomicTypeExprContextAttrs<'input>) -> Rc<AtomicTypeExprContextAll<'input>>  {
		Rc::new(
			AtomicTypeExprContextAll::TypeExprParenContext(
				BaseParserRuleContext::copy_from(ctx,TypeExprParenContextExt{
        			inner:None, 
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

impl<'input, I, H> LibSLParser<'input, I, H>
where
    I: TokenStream<'input, TF = LocalTokenFactory<'input> > + TidAble<'input>,
    H: ErrorStrategy<'input,BaseParserType<'input,I>>
{
	pub fn atomicTypeExpr(&mut self,)
	-> Result<Rc<AtomicTypeExprContextAll<'input>>,ANTLRError> {
		let mut recog = self;
		let _parentctx = recog.ctx.take();
		let mut _localctx = AtomicTypeExprContextExt::new(_parentctx.clone(), recog.base.get_state());
        recog.base.enter_rule(_localctx.clone(), 144, RULE_atomicTypeExpr);
        let mut _localctx: Rc<AtomicTypeExprContextAll> = _localctx;
		let result: Result<(), ANTLRError> = (|| {

			recog.base.set_state(1005);
			recog.err_handler.sync(&mut recog.base)?;
			match recog.base.input.la(1) {
			 L_PAREN 
				=> {
					let tmp = TypeExprParenContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 1);
					_localctx = tmp;
					{
					recog.base.set_state(998);
					recog.base.match_token(L_PAREN,&mut recog.err_handler)?;

					/*InvokeRule typeExpr*/
					recog.base.set_state(999);
					let tmp = recog.typeExpr_rec(0)?;
					if let AtomicTypeExprContextAll::TypeExprParenContext(ctx) = cast_mut::<_,AtomicTypeExprContextAll >(&mut _localctx){
					ctx.inner = Some(tmp.clone()); } else {unreachable!("cant cast");}  

					recog.base.set_state(1000);
					recog.base.match_token(R_PAREN,&mut recog.err_handler)?;

					}
				}

			 TRUE | FALSE | NULL | IntegerLit | FloatLit | StringLit | CharacterLit 
				=> {
					let tmp = TypeExprPrimitiveLitContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 2);
					_localctx = tmp;
					{
					/*InvokeRule primitiveLit*/
					recog.base.set_state(1002);
					let tmp = recog.primitiveLit()?;
					if let AtomicTypeExprContextAll::TypeExprPrimitiveLitContext(ctx) = cast_mut::<_,AtomicTypeExprContextAll >(&mut _localctx){
					ctx.lit = Some(tmp.clone()); } else {unreachable!("cant cast");}  

					}
				}

			 IMPLEMENTS | STATIC | PURE | Identifier 
				=> {
					let tmp = TypeExprNameContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 3);
					_localctx = tmp;
					{
					/*InvokeRule nameTypeExpr*/
					recog.base.set_state(1003);
					recog.nameTypeExpr()?;

					}
				}

			 ASTERISK 
				=> {
					let tmp = TypeExprPointerContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 4);
					_localctx = tmp;
					{
					/*InvokeRule pointerTypeExpr*/
					recog.base.set_state(1004);
					recog.pointerTypeExpr()?;

					}
				}

				_ => Err(ANTLRError::NoAltError(NoViableAltError::new(&mut recog.base)))?
			}
			Ok(())
		})();
		match result {
		Ok(_)=>{},
        Err(e @ ANTLRError::FallThrough(_)) => return Err(e),
		Err(ref re) => {
				//_localctx.exception = re;
				recog.err_handler.report_error(&mut recog.base, re);
				recog.err_handler.recover(&mut recog.base, re)?;
			}
		}
		recog.base.exit_rule();

		Ok(_localctx)
	}
}
//------------------- typeExpr ----------------
#[derive(Debug)]
pub enum TypeExprContextAll<'input>{
	TypeExprIntersectionContext(TypeExprIntersectionContext<'input>),
	TypeExprAtomicContext(TypeExprAtomicContext<'input>),
	TypeExprUnionContext(TypeExprUnionContext<'input>),
Error(TypeExprContext<'input>)
}
antlr_rust::tid!{TypeExprContextAll<'a>}

impl<'input> antlr_rust::parser_rule_context::DerefSeal for TypeExprContextAll<'input>{}

impl<'input> LibSLParserContext<'input> for TypeExprContextAll<'input>{}

impl<'input> Deref for TypeExprContextAll<'input>{
	type Target = dyn TypeExprContextAttrs<'input> + 'input;
	fn deref(&self) -> &Self::Target{
		use TypeExprContextAll::*;
		match self{
			TypeExprIntersectionContext(inner) => inner,
			TypeExprAtomicContext(inner) => inner,
			TypeExprUnionContext(inner) => inner,
Error(inner) => inner
		}
	}
}
impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for TypeExprContextAll<'input>{
    fn enter(&self, listener: &mut (dyn LibSLParserListener<'input> + 'a)) { self.deref().enter(listener) }
    fn exit(&self, listener: &mut (dyn LibSLParserListener<'input> + 'a)) { self.deref().exit(listener) }
}



pub type TypeExprContext<'input> = BaseParserRuleContext<'input,TypeExprContextExt<'input>>;

#[derive(Clone)]
pub struct TypeExprContextExt<'input>{
ph:PhantomData<&'input str>
}

impl<'input> LibSLParserContext<'input> for TypeExprContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for TypeExprContext<'input>{
}

impl<'input> CustomRuleContext<'input> for TypeExprContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_typeExpr }
	//fn type_rule_index() -> usize where Self: Sized { RULE_typeExpr }
}
antlr_rust::tid!{TypeExprContextExt<'a>}

impl<'input> TypeExprContextExt<'input>{
	fn new(parent: Option<Rc<dyn LibSLParserContext<'input> + 'input > >, invoking_state: isize) -> Rc<TypeExprContextAll<'input>> {
		Rc::new(
		TypeExprContextAll::Error(
			BaseParserRuleContext::new_parser_ctx(parent, invoking_state,TypeExprContextExt{
				ph:PhantomData
			}),
		)
		)
	}
}

pub trait TypeExprContextAttrs<'input>: LibSLParserContext<'input> + BorrowMut<TypeExprContextExt<'input>>{


}

impl<'input> TypeExprContextAttrs<'input> for TypeExprContext<'input>{}

pub type TypeExprIntersectionContext<'input> = BaseParserRuleContext<'input,TypeExprIntersectionContextExt<'input>>;

pub trait TypeExprIntersectionContextAttrs<'input>: LibSLParserContext<'input>{
	/// Retrieves first TerminalNode corresponding to token AMP
	/// Returns `None` if there is no child corresponding to token AMP
	fn AMP(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(AMP, 0)
	}
	fn typeExpr_all(&self) ->  Vec<Rc<TypeExprContextAll<'input>>> where Self:Sized{
		self.children_of_type()
	}
	fn typeExpr(&self, i: usize) -> Option<Rc<TypeExprContextAll<'input>>> where Self:Sized{
		self.child_of_type(i)
	}
}

impl<'input> TypeExprIntersectionContextAttrs<'input> for TypeExprIntersectionContext<'input>{}

pub struct TypeExprIntersectionContextExt<'input>{
	__base:TypeExprContextExt<'input>,
	pub lhs: Option<Rc<TypeExprContextAll<'input>>>,
	pub rhs: Option<Rc<TypeExprContextAll<'input>>>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{TypeExprIntersectionContextExt<'a>}

impl<'input> LibSLParserContext<'input> for TypeExprIntersectionContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for TypeExprIntersectionContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_TypeExprIntersection(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_TypeExprIntersection(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for TypeExprIntersectionContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_typeExpr }
	//fn type_rule_index() -> usize where Self: Sized { RULE_typeExpr }
}

impl<'input> Borrow<TypeExprContextExt<'input>> for TypeExprIntersectionContext<'input>{
	fn borrow(&self) -> &TypeExprContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<TypeExprContextExt<'input>> for TypeExprIntersectionContext<'input>{
	fn borrow_mut(&mut self) -> &mut TypeExprContextExt<'input> { &mut self.__base }
}

impl<'input> TypeExprContextAttrs<'input> for TypeExprIntersectionContext<'input> {}

impl<'input> TypeExprIntersectionContextExt<'input>{
	fn new(ctx: &dyn TypeExprContextAttrs<'input>) -> Rc<TypeExprContextAll<'input>>  {
		Rc::new(
			TypeExprContextAll::TypeExprIntersectionContext(
				BaseParserRuleContext::copy_from(ctx,TypeExprIntersectionContextExt{
        			lhs:None, rhs:None, 
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type TypeExprAtomicContext<'input> = BaseParserRuleContext<'input,TypeExprAtomicContextExt<'input>>;

pub trait TypeExprAtomicContextAttrs<'input>: LibSLParserContext<'input>{
	fn atomicTypeExpr(&self) -> Option<Rc<AtomicTypeExprContextAll<'input>>> where Self:Sized{
		self.child_of_type(0)
	}
}

impl<'input> TypeExprAtomicContextAttrs<'input> for TypeExprAtomicContext<'input>{}

pub struct TypeExprAtomicContextExt<'input>{
	__base:TypeExprContextExt<'input>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{TypeExprAtomicContextExt<'a>}

impl<'input> LibSLParserContext<'input> for TypeExprAtomicContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for TypeExprAtomicContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_TypeExprAtomic(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_TypeExprAtomic(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for TypeExprAtomicContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_typeExpr }
	//fn type_rule_index() -> usize where Self: Sized { RULE_typeExpr }
}

impl<'input> Borrow<TypeExprContextExt<'input>> for TypeExprAtomicContext<'input>{
	fn borrow(&self) -> &TypeExprContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<TypeExprContextExt<'input>> for TypeExprAtomicContext<'input>{
	fn borrow_mut(&mut self) -> &mut TypeExprContextExt<'input> { &mut self.__base }
}

impl<'input> TypeExprContextAttrs<'input> for TypeExprAtomicContext<'input> {}

impl<'input> TypeExprAtomicContextExt<'input>{
	fn new(ctx: &dyn TypeExprContextAttrs<'input>) -> Rc<TypeExprContextAll<'input>>  {
		Rc::new(
			TypeExprContextAll::TypeExprAtomicContext(
				BaseParserRuleContext::copy_from(ctx,TypeExprAtomicContextExt{
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type TypeExprUnionContext<'input> = BaseParserRuleContext<'input,TypeExprUnionContextExt<'input>>;

pub trait TypeExprUnionContextAttrs<'input>: LibSLParserContext<'input>{
	/// Retrieves first TerminalNode corresponding to token PIPE
	/// Returns `None` if there is no child corresponding to token PIPE
	fn PIPE(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(PIPE, 0)
	}
	fn typeExpr_all(&self) ->  Vec<Rc<TypeExprContextAll<'input>>> where Self:Sized{
		self.children_of_type()
	}
	fn typeExpr(&self, i: usize) -> Option<Rc<TypeExprContextAll<'input>>> where Self:Sized{
		self.child_of_type(i)
	}
}

impl<'input> TypeExprUnionContextAttrs<'input> for TypeExprUnionContext<'input>{}

pub struct TypeExprUnionContextExt<'input>{
	__base:TypeExprContextExt<'input>,
	pub lhs: Option<Rc<TypeExprContextAll<'input>>>,
	pub rhs: Option<Rc<TypeExprContextAll<'input>>>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{TypeExprUnionContextExt<'a>}

impl<'input> LibSLParserContext<'input> for TypeExprUnionContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for TypeExprUnionContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_TypeExprUnion(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_TypeExprUnion(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for TypeExprUnionContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_typeExpr }
	//fn type_rule_index() -> usize where Self: Sized { RULE_typeExpr }
}

impl<'input> Borrow<TypeExprContextExt<'input>> for TypeExprUnionContext<'input>{
	fn borrow(&self) -> &TypeExprContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<TypeExprContextExt<'input>> for TypeExprUnionContext<'input>{
	fn borrow_mut(&mut self) -> &mut TypeExprContextExt<'input> { &mut self.__base }
}

impl<'input> TypeExprContextAttrs<'input> for TypeExprUnionContext<'input> {}

impl<'input> TypeExprUnionContextExt<'input>{
	fn new(ctx: &dyn TypeExprContextAttrs<'input>) -> Rc<TypeExprContextAll<'input>>  {
		Rc::new(
			TypeExprContextAll::TypeExprUnionContext(
				BaseParserRuleContext::copy_from(ctx,TypeExprUnionContextExt{
        			lhs:None, rhs:None, 
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

impl<'input, I, H> LibSLParser<'input, I, H>
where
    I: TokenStream<'input, TF = LocalTokenFactory<'input> > + TidAble<'input>,
    H: ErrorStrategy<'input,BaseParserType<'input,I>>
{
	pub fn  typeExpr(&mut self,)
	-> Result<Rc<TypeExprContextAll<'input>>,ANTLRError> {
		self.typeExpr_rec(0)
	}

	fn typeExpr_rec(&mut self, _p: isize)
	-> Result<Rc<TypeExprContextAll<'input>>,ANTLRError> {
		let recog = self;
		let _parentctx = recog.ctx.take();
		let _parentState = recog.base.get_state();
		let mut _localctx = TypeExprContextExt::new(_parentctx.clone(), recog.base.get_state());
		recog.base.enter_recursion_rule(_localctx.clone(), 146, RULE_typeExpr, _p);
	    let mut _localctx: Rc<TypeExprContextAll> = _localctx;
        let mut _prevctx = _localctx.clone();
		let _startState = 146;
		let result: Result<(), ANTLRError> = (|| {
			let mut _alt: isize;
			//recog.base.enter_outer_alt(_localctx.clone(), 1);
			recog.base.enter_outer_alt(None, 1);
			{
			{
			let mut tmp = TypeExprAtomicContextExt::new(&**_localctx);
			recog.ctx = Some(tmp.clone());
			recog.trigger_enter_rule_event();
			_localctx = tmp;
			_prevctx = _localctx.clone();


			/*InvokeRule atomicTypeExpr*/
			recog.base.set_state(1008);
			recog.atomicTypeExpr()?;

			}

			let tmp = recog.input.lt(-1).cloned();
			recog.ctx.as_ref().unwrap().set_stop(tmp);
			recog.base.set_state(1018);
			recog.err_handler.sync(&mut recog.base)?;
			_alt = recog.interpreter.adaptive_predict(133,&mut recog.base)?;
			while { _alt!=2 && _alt!=INVALID_ALT } {
				if _alt==1 {
					recog.trigger_exit_rule_event();
					_prevctx = _localctx.clone();
					{
					recog.base.set_state(1016);
					recog.err_handler.sync(&mut recog.base)?;
					match  recog.interpreter.adaptive_predict(132,&mut recog.base)? {
						1 =>{
							{
							/*recRuleLabeledAltStartAction*/
							let mut tmp = TypeExprIntersectionContextExt::new(&**TypeExprContextExt::new(_parentctx.clone(), _parentState));
							if let TypeExprContextAll::TypeExprIntersectionContext(ctx) = cast_mut::<_,TypeExprContextAll >(&mut tmp){
								ctx.lhs = Some(_prevctx.clone());
							} else {unreachable!("cant cast");}
							recog.push_new_recursion_context(tmp.clone(), _startState, RULE_typeExpr);
							_localctx = tmp;
							recog.base.set_state(1010);
							if !({recog.precpred(None, 2)}) {
								Err(FailedPredicateError::new(&mut recog.base, Some("recog.precpred(None, 2)".to_owned()), None))?;
							}
							recog.base.set_state(1011);
							recog.base.match_token(AMP,&mut recog.err_handler)?;

							/*InvokeRule typeExpr*/
							recog.base.set_state(1012);
							let tmp = recog.typeExpr_rec(3)?;
							if let TypeExprContextAll::TypeExprIntersectionContext(ctx) = cast_mut::<_,TypeExprContextAll >(&mut _localctx){
							ctx.rhs = Some(tmp.clone()); } else {unreachable!("cant cast");}  

							}
						}
					,
						2 =>{
							{
							/*recRuleLabeledAltStartAction*/
							let mut tmp = TypeExprUnionContextExt::new(&**TypeExprContextExt::new(_parentctx.clone(), _parentState));
							if let TypeExprContextAll::TypeExprUnionContext(ctx) = cast_mut::<_,TypeExprContextAll >(&mut tmp){
								ctx.lhs = Some(_prevctx.clone());
							} else {unreachable!("cant cast");}
							recog.push_new_recursion_context(tmp.clone(), _startState, RULE_typeExpr);
							_localctx = tmp;
							recog.base.set_state(1013);
							if !({recog.precpred(None, 1)}) {
								Err(FailedPredicateError::new(&mut recog.base, Some("recog.precpred(None, 1)".to_owned()), None))?;
							}
							recog.base.set_state(1014);
							recog.base.match_token(PIPE,&mut recog.err_handler)?;

							/*InvokeRule typeExpr*/
							recog.base.set_state(1015);
							let tmp = recog.typeExpr_rec(2)?;
							if let TypeExprContextAll::TypeExprUnionContext(ctx) = cast_mut::<_,TypeExprContextAll >(&mut _localctx){
							ctx.rhs = Some(tmp.clone()); } else {unreachable!("cant cast");}  

							}
						}

						_ => {}
					}
					} 
				}
				recog.base.set_state(1020);
				recog.err_handler.sync(&mut recog.base)?;
				_alt = recog.interpreter.adaptive_predict(133,&mut recog.base)?;
			}
			}
			Ok(())
		})();
		match result {
		Ok(_) => {},
        Err(e @ ANTLRError::FallThrough(_)) => return Err(e),
		Err(ref re)=>{
			//_localctx.exception = re;
			recog.err_handler.report_error(&mut recog.base, re);
	        recog.err_handler.recover(&mut recog.base, re)?;}
		}
		recog.base.unroll_recursion_context(_parentctx);

		Ok(_localctx)
	}
}
//------------------- nameTypeExpr ----------------
pub type NameTypeExprContextAll<'input> = NameTypeExprContext<'input>;


pub type NameTypeExprContext<'input> = BaseParserRuleContext<'input,NameTypeExprContextExt<'input>>;

#[derive(Clone)]
pub struct NameTypeExprContextExt<'input>{
	pub typeName: Option<Rc<FullNameContextAll<'input>>>,
	pub typeArgs: Option<Rc<TypeArgSpecContextAll<'input>>>,
ph:PhantomData<&'input str>
}

impl<'input> LibSLParserContext<'input> for NameTypeExprContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for NameTypeExprContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_nameTypeExpr(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_nameTypeExpr(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for NameTypeExprContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_nameTypeExpr }
	//fn type_rule_index() -> usize where Self: Sized { RULE_nameTypeExpr }
}
antlr_rust::tid!{NameTypeExprContextExt<'a>}

impl<'input> NameTypeExprContextExt<'input>{
	fn new(parent: Option<Rc<dyn LibSLParserContext<'input> + 'input > >, invoking_state: isize) -> Rc<NameTypeExprContextAll<'input>> {
		Rc::new(
			BaseParserRuleContext::new_parser_ctx(parent, invoking_state,NameTypeExprContextExt{
				typeName: None, typeArgs: None, 
				ph:PhantomData
			}),
		)
	}
}

pub trait NameTypeExprContextAttrs<'input>: LibSLParserContext<'input> + BorrowMut<NameTypeExprContextExt<'input>>{

fn fullName(&self) -> Option<Rc<FullNameContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}
fn typeArgSpec(&self) -> Option<Rc<TypeArgSpecContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}

}

impl<'input> NameTypeExprContextAttrs<'input> for NameTypeExprContext<'input>{}

impl<'input, I, H> LibSLParser<'input, I, H>
where
    I: TokenStream<'input, TF = LocalTokenFactory<'input> > + TidAble<'input>,
    H: ErrorStrategy<'input,BaseParserType<'input,I>>
{
	pub fn nameTypeExpr(&mut self,)
	-> Result<Rc<NameTypeExprContextAll<'input>>,ANTLRError> {
		let mut recog = self;
		let _parentctx = recog.ctx.take();
		let mut _localctx = NameTypeExprContextExt::new(_parentctx.clone(), recog.base.get_state());
        recog.base.enter_rule(_localctx.clone(), 148, RULE_nameTypeExpr);
        let mut _localctx: Rc<NameTypeExprContextAll> = _localctx;
		let result: Result<(), ANTLRError> = (|| {

			//recog.base.enter_outer_alt(_localctx.clone(), 1);
			recog.base.enter_outer_alt(None, 1);
			{
			/*InvokeRule fullName*/
			recog.base.set_state(1021);
			let tmp = recog.fullName()?;
			 cast_mut::<_,NameTypeExprContext >(&mut _localctx).typeName = Some(tmp.clone());
			  

			recog.base.set_state(1023);
			recog.err_handler.sync(&mut recog.base)?;
			match  recog.interpreter.adaptive_predict(134,&mut recog.base)? {
				x if x == 1=>{
					{
					/*InvokeRule typeArgSpec*/
					recog.base.set_state(1022);
					let tmp = recog.typeArgSpec()?;
					 cast_mut::<_,NameTypeExprContext >(&mut _localctx).typeArgs = Some(tmp.clone());
					  

					}
				}

				_ => {}
			}
			}
			Ok(())
		})();
		match result {
		Ok(_)=>{},
        Err(e @ ANTLRError::FallThrough(_)) => return Err(e),
		Err(ref re) => {
				//_localctx.exception = re;
				recog.err_handler.report_error(&mut recog.base, re);
				recog.err_handler.recover(&mut recog.base, re)?;
			}
		}
		recog.base.exit_rule();

		Ok(_localctx)
	}
}
//------------------- pointerTypeExpr ----------------
pub type PointerTypeExprContextAll<'input> = PointerTypeExprContext<'input>;


pub type PointerTypeExprContext<'input> = BaseParserRuleContext<'input,PointerTypeExprContextExt<'input>>;

#[derive(Clone)]
pub struct PointerTypeExprContextExt<'input>{
	pub base: Option<Rc<AtomicTypeExprContextAll<'input>>>,
ph:PhantomData<&'input str>
}

impl<'input> LibSLParserContext<'input> for PointerTypeExprContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for PointerTypeExprContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_pointerTypeExpr(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_pointerTypeExpr(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for PointerTypeExprContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_pointerTypeExpr }
	//fn type_rule_index() -> usize where Self: Sized { RULE_pointerTypeExpr }
}
antlr_rust::tid!{PointerTypeExprContextExt<'a>}

impl<'input> PointerTypeExprContextExt<'input>{
	fn new(parent: Option<Rc<dyn LibSLParserContext<'input> + 'input > >, invoking_state: isize) -> Rc<PointerTypeExprContextAll<'input>> {
		Rc::new(
			BaseParserRuleContext::new_parser_ctx(parent, invoking_state,PointerTypeExprContextExt{
				base: None, 
				ph:PhantomData
			}),
		)
	}
}

pub trait PointerTypeExprContextAttrs<'input>: LibSLParserContext<'input> + BorrowMut<PointerTypeExprContextExt<'input>>{

/// Retrieves first TerminalNode corresponding to token ASTERISK
/// Returns `None` if there is no child corresponding to token ASTERISK
fn ASTERISK(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(ASTERISK, 0)
}
fn atomicTypeExpr(&self) -> Option<Rc<AtomicTypeExprContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}

}

impl<'input> PointerTypeExprContextAttrs<'input> for PointerTypeExprContext<'input>{}

impl<'input, I, H> LibSLParser<'input, I, H>
where
    I: TokenStream<'input, TF = LocalTokenFactory<'input> > + TidAble<'input>,
    H: ErrorStrategy<'input,BaseParserType<'input,I>>
{
	pub fn pointerTypeExpr(&mut self,)
	-> Result<Rc<PointerTypeExprContextAll<'input>>,ANTLRError> {
		let mut recog = self;
		let _parentctx = recog.ctx.take();
		let mut _localctx = PointerTypeExprContextExt::new(_parentctx.clone(), recog.base.get_state());
        recog.base.enter_rule(_localctx.clone(), 150, RULE_pointerTypeExpr);
        let mut _localctx: Rc<PointerTypeExprContextAll> = _localctx;
		let result: Result<(), ANTLRError> = (|| {

			//recog.base.enter_outer_alt(_localctx.clone(), 1);
			recog.base.enter_outer_alt(None, 1);
			{
			recog.base.set_state(1025);
			recog.base.match_token(ASTERISK,&mut recog.err_handler)?;

			/*InvokeRule atomicTypeExpr*/
			recog.base.set_state(1026);
			let tmp = recog.atomicTypeExpr()?;
			 cast_mut::<_,PointerTypeExprContext >(&mut _localctx).base = Some(tmp.clone());
			  

			}
			Ok(())
		})();
		match result {
		Ok(_)=>{},
        Err(e @ ANTLRError::FallThrough(_)) => return Err(e),
		Err(ref re) => {
				//_localctx.exception = re;
				recog.err_handler.report_error(&mut recog.base, re);
				recog.err_handler.recover(&mut recog.base, re)?;
			}
		}
		recog.base.exit_rule();

		Ok(_localctx)
	}
}
//------------------- typeArgSpec ----------------
pub type TypeArgSpecContextAll<'input> = TypeArgSpecContext<'input>;


pub type TypeArgSpecContext<'input> = BaseParserRuleContext<'input,TypeArgSpecContextExt<'input>>;

#[derive(Clone)]
pub struct TypeArgSpecContextExt<'input>{
	pub list: Option<Rc<TypeArgListContextAll<'input>>>,
ph:PhantomData<&'input str>
}

impl<'input> LibSLParserContext<'input> for TypeArgSpecContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for TypeArgSpecContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_typeArgSpec(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_typeArgSpec(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for TypeArgSpecContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_typeArgSpec }
	//fn type_rule_index() -> usize where Self: Sized { RULE_typeArgSpec }
}
antlr_rust::tid!{TypeArgSpecContextExt<'a>}

impl<'input> TypeArgSpecContextExt<'input>{
	fn new(parent: Option<Rc<dyn LibSLParserContext<'input> + 'input > >, invoking_state: isize) -> Rc<TypeArgSpecContextAll<'input>> {
		Rc::new(
			BaseParserRuleContext::new_parser_ctx(parent, invoking_state,TypeArgSpecContextExt{
				list: None, 
				ph:PhantomData
			}),
		)
	}
}

pub trait TypeArgSpecContextAttrs<'input>: LibSLParserContext<'input> + BorrowMut<TypeArgSpecContextExt<'input>>{

/// Retrieves first TerminalNode corresponding to token L_ANGLE
/// Returns `None` if there is no child corresponding to token L_ANGLE
fn L_ANGLE(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(L_ANGLE, 0)
}
/// Retrieves first TerminalNode corresponding to token R_ANGLE
/// Returns `None` if there is no child corresponding to token R_ANGLE
fn R_ANGLE(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(R_ANGLE, 0)
}
fn typeArgList(&self) -> Option<Rc<TypeArgListContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}
/// Retrieves first TerminalNode corresponding to token COMMA
/// Returns `None` if there is no child corresponding to token COMMA
fn COMMA(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(COMMA, 0)
}

}

impl<'input> TypeArgSpecContextAttrs<'input> for TypeArgSpecContext<'input>{}

impl<'input, I, H> LibSLParser<'input, I, H>
where
    I: TokenStream<'input, TF = LocalTokenFactory<'input> > + TidAble<'input>,
    H: ErrorStrategy<'input,BaseParserType<'input,I>>
{
	pub fn typeArgSpec(&mut self,)
	-> Result<Rc<TypeArgSpecContextAll<'input>>,ANTLRError> {
		let mut recog = self;
		let _parentctx = recog.ctx.take();
		let mut _localctx = TypeArgSpecContextExt::new(_parentctx.clone(), recog.base.get_state());
        recog.base.enter_rule(_localctx.clone(), 152, RULE_typeArgSpec);
        let mut _localctx: Rc<TypeArgSpecContextAll> = _localctx;
		let mut _la: isize = -1;
		let result: Result<(), ANTLRError> = (|| {

			//recog.base.enter_outer_alt(_localctx.clone(), 1);
			recog.base.enter_outer_alt(None, 1);
			{
			recog.base.set_state(1028);
			recog.base.match_token(L_ANGLE,&mut recog.err_handler)?;

			recog.base.set_state(1033);
			recog.err_handler.sync(&mut recog.base)?;
			_la = recog.base.input.la(1);
			if _la==L_PAREN || _la==ASTERISK || ((((_la - 73)) & !0x3f) == 0 && ((1usize << (_la - 73)) & 32171779) != 0) {
				{
				/*InvokeRule typeArgList*/
				recog.base.set_state(1029);
				let tmp = recog.typeArgList()?;
				 cast_mut::<_,TypeArgSpecContext >(&mut _localctx).list = Some(tmp.clone());
				  

				recog.base.set_state(1031);
				recog.err_handler.sync(&mut recog.base)?;
				_la = recog.base.input.la(1);
				if _la==COMMA {
					{
					recog.base.set_state(1030);
					recog.base.match_token(COMMA,&mut recog.err_handler)?;

					}
				}

				}
			}

			recog.base.set_state(1035);
			recog.base.match_token(R_ANGLE,&mut recog.err_handler)?;

			}
			Ok(())
		})();
		match result {
		Ok(_)=>{},
        Err(e @ ANTLRError::FallThrough(_)) => return Err(e),
		Err(ref re) => {
				//_localctx.exception = re;
				recog.err_handler.report_error(&mut recog.base, re);
				recog.err_handler.recover(&mut recog.base, re)?;
			}
		}
		recog.base.exit_rule();

		Ok(_localctx)
	}
}
//------------------- typeArgList ----------------
pub type TypeArgListContextAll<'input> = TypeArgListContext<'input>;


pub type TypeArgListContext<'input> = BaseParserRuleContext<'input,TypeArgListContextExt<'input>>;

#[derive(Clone)]
pub struct TypeArgListContextExt<'input>{
	pub typeArg: Option<Rc<TypeArgContextAll<'input>>>,
	pub typeArgs:Vec<Rc<TypeArgContextAll<'input>>>,
ph:PhantomData<&'input str>
}

impl<'input> LibSLParserContext<'input> for TypeArgListContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for TypeArgListContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_typeArgList(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_typeArgList(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for TypeArgListContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_typeArgList }
	//fn type_rule_index() -> usize where Self: Sized { RULE_typeArgList }
}
antlr_rust::tid!{TypeArgListContextExt<'a>}

impl<'input> TypeArgListContextExt<'input>{
	fn new(parent: Option<Rc<dyn LibSLParserContext<'input> + 'input > >, invoking_state: isize) -> Rc<TypeArgListContextAll<'input>> {
		Rc::new(
			BaseParserRuleContext::new_parser_ctx(parent, invoking_state,TypeArgListContextExt{
				typeArg: None, 
				typeArgs: Vec::new(), 
				ph:PhantomData
			}),
		)
	}
}

pub trait TypeArgListContextAttrs<'input>: LibSLParserContext<'input> + BorrowMut<TypeArgListContextExt<'input>>{

fn typeArg_all(&self) ->  Vec<Rc<TypeArgContextAll<'input>>> where Self:Sized{
	self.children_of_type()
}
fn typeArg(&self, i: usize) -> Option<Rc<TypeArgContextAll<'input>>> where Self:Sized{
	self.child_of_type(i)
}
/// Retrieves all `TerminalNode`s corresponding to token COMMA in current rule
fn COMMA_all(&self) -> Vec<Rc<TerminalNode<'input,LibSLParserContextType>>>  where Self:Sized{
	self.get_tokens(COMMA)
}
/// Retrieves 'i's TerminalNode corresponding to token COMMA, starting from 0.
/// Returns `None` if number of children corresponding to token COMMA is less or equal than `i`.
fn COMMA(&self, i: usize) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(COMMA, i)
}

}

impl<'input> TypeArgListContextAttrs<'input> for TypeArgListContext<'input>{}

impl<'input, I, H> LibSLParser<'input, I, H>
where
    I: TokenStream<'input, TF = LocalTokenFactory<'input> > + TidAble<'input>,
    H: ErrorStrategy<'input,BaseParserType<'input,I>>
{
	pub fn typeArgList(&mut self,)
	-> Result<Rc<TypeArgListContextAll<'input>>,ANTLRError> {
		let mut recog = self;
		let _parentctx = recog.ctx.take();
		let mut _localctx = TypeArgListContextExt::new(_parentctx.clone(), recog.base.get_state());
        recog.base.enter_rule(_localctx.clone(), 154, RULE_typeArgList);
        let mut _localctx: Rc<TypeArgListContextAll> = _localctx;
		let result: Result<(), ANTLRError> = (|| {

			let mut _alt: isize;
			//recog.base.enter_outer_alt(_localctx.clone(), 1);
			recog.base.enter_outer_alt(None, 1);
			{
			/*InvokeRule typeArg*/
			recog.base.set_state(1037);
			let tmp = recog.typeArg()?;
			 cast_mut::<_,TypeArgListContext >(&mut _localctx).typeArg = Some(tmp.clone());
			  

			let temp =  cast_mut::<_,TypeArgListContext >(&mut _localctx).typeArg.clone().unwrap()
			 ;
			 cast_mut::<_,TypeArgListContext >(&mut _localctx).typeArgs.push(temp);
			  
			recog.base.set_state(1042);
			recog.err_handler.sync(&mut recog.base)?;
			_alt = recog.interpreter.adaptive_predict(137,&mut recog.base)?;
			while { _alt!=2 && _alt!=INVALID_ALT } {
				if _alt==1 {
					{
					{
					recog.base.set_state(1038);
					recog.base.match_token(COMMA,&mut recog.err_handler)?;

					/*InvokeRule typeArg*/
					recog.base.set_state(1039);
					let tmp = recog.typeArg()?;
					 cast_mut::<_,TypeArgListContext >(&mut _localctx).typeArg = Some(tmp.clone());
					  

					let temp =  cast_mut::<_,TypeArgListContext >(&mut _localctx).typeArg.clone().unwrap()
					 ;
					 cast_mut::<_,TypeArgListContext >(&mut _localctx).typeArgs.push(temp);
					  
					}
					} 
				}
				recog.base.set_state(1044);
				recog.err_handler.sync(&mut recog.base)?;
				_alt = recog.interpreter.adaptive_predict(137,&mut recog.base)?;
			}
			}
			Ok(())
		})();
		match result {
		Ok(_)=>{},
        Err(e @ ANTLRError::FallThrough(_)) => return Err(e),
		Err(ref re) => {
				//_localctx.exception = re;
				recog.err_handler.report_error(&mut recog.base, re);
				recog.err_handler.recover(&mut recog.base, re)?;
			}
		}
		recog.base.exit_rule();

		Ok(_localctx)
	}
}
//------------------- typeArg ----------------
#[derive(Debug)]
pub enum TypeArgContextAll<'input>{
	TypeArgTypeExprContext(TypeArgTypeExprContext<'input>),
	TypeArgWildcardContext(TypeArgWildcardContext<'input>),
Error(TypeArgContext<'input>)
}
antlr_rust::tid!{TypeArgContextAll<'a>}

impl<'input> antlr_rust::parser_rule_context::DerefSeal for TypeArgContextAll<'input>{}

impl<'input> LibSLParserContext<'input> for TypeArgContextAll<'input>{}

impl<'input> Deref for TypeArgContextAll<'input>{
	type Target = dyn TypeArgContextAttrs<'input> + 'input;
	fn deref(&self) -> &Self::Target{
		use TypeArgContextAll::*;
		match self{
			TypeArgTypeExprContext(inner) => inner,
			TypeArgWildcardContext(inner) => inner,
Error(inner) => inner
		}
	}
}
impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for TypeArgContextAll<'input>{
    fn enter(&self, listener: &mut (dyn LibSLParserListener<'input> + 'a)) { self.deref().enter(listener) }
    fn exit(&self, listener: &mut (dyn LibSLParserListener<'input> + 'a)) { self.deref().exit(listener) }
}



pub type TypeArgContext<'input> = BaseParserRuleContext<'input,TypeArgContextExt<'input>>;

#[derive(Clone)]
pub struct TypeArgContextExt<'input>{
ph:PhantomData<&'input str>
}

impl<'input> LibSLParserContext<'input> for TypeArgContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for TypeArgContext<'input>{
}

impl<'input> CustomRuleContext<'input> for TypeArgContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_typeArg }
	//fn type_rule_index() -> usize where Self: Sized { RULE_typeArg }
}
antlr_rust::tid!{TypeArgContextExt<'a>}

impl<'input> TypeArgContextExt<'input>{
	fn new(parent: Option<Rc<dyn LibSLParserContext<'input> + 'input > >, invoking_state: isize) -> Rc<TypeArgContextAll<'input>> {
		Rc::new(
		TypeArgContextAll::Error(
			BaseParserRuleContext::new_parser_ctx(parent, invoking_state,TypeArgContextExt{
				ph:PhantomData
			}),
		)
		)
	}
}

pub trait TypeArgContextAttrs<'input>: LibSLParserContext<'input> + BorrowMut<TypeArgContextExt<'input>>{


}

impl<'input> TypeArgContextAttrs<'input> for TypeArgContext<'input>{}

pub type TypeArgTypeExprContext<'input> = BaseParserRuleContext<'input,TypeArgTypeExprContextExt<'input>>;

pub trait TypeArgTypeExprContextAttrs<'input>: LibSLParserContext<'input>{
	fn typeExpr(&self) -> Option<Rc<TypeExprContextAll<'input>>> where Self:Sized{
		self.child_of_type(0)
	}
	fn varianceSpec(&self) -> Option<Rc<VarianceSpecContextAll<'input>>> where Self:Sized{
		self.child_of_type(0)
	}
}

impl<'input> TypeArgTypeExprContextAttrs<'input> for TypeArgTypeExprContext<'input>{}

pub struct TypeArgTypeExprContextExt<'input>{
	__base:TypeArgContextExt<'input>,
	pub variance: Option<Rc<VarianceSpecContextAll<'input>>>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{TypeArgTypeExprContextExt<'a>}

impl<'input> LibSLParserContext<'input> for TypeArgTypeExprContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for TypeArgTypeExprContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_TypeArgTypeExpr(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_TypeArgTypeExpr(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for TypeArgTypeExprContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_typeArg }
	//fn type_rule_index() -> usize where Self: Sized { RULE_typeArg }
}

impl<'input> Borrow<TypeArgContextExt<'input>> for TypeArgTypeExprContext<'input>{
	fn borrow(&self) -> &TypeArgContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<TypeArgContextExt<'input>> for TypeArgTypeExprContext<'input>{
	fn borrow_mut(&mut self) -> &mut TypeArgContextExt<'input> { &mut self.__base }
}

impl<'input> TypeArgContextAttrs<'input> for TypeArgTypeExprContext<'input> {}

impl<'input> TypeArgTypeExprContextExt<'input>{
	fn new(ctx: &dyn TypeArgContextAttrs<'input>) -> Rc<TypeArgContextAll<'input>>  {
		Rc::new(
			TypeArgContextAll::TypeArgTypeExprContext(
				BaseParserRuleContext::copy_from(ctx,TypeArgTypeExprContextExt{
        			variance:None, 
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type TypeArgWildcardContext<'input> = BaseParserRuleContext<'input,TypeArgWildcardContextExt<'input>>;

pub trait TypeArgWildcardContextAttrs<'input>: LibSLParserContext<'input>{
	/// Retrieves first TerminalNode corresponding to token QUESTION
	/// Returns `None` if there is no child corresponding to token QUESTION
	fn QUESTION(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(QUESTION, 0)
	}
}

impl<'input> TypeArgWildcardContextAttrs<'input> for TypeArgWildcardContext<'input>{}

pub struct TypeArgWildcardContextExt<'input>{
	__base:TypeArgContextExt<'input>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{TypeArgWildcardContextExt<'a>}

impl<'input> LibSLParserContext<'input> for TypeArgWildcardContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for TypeArgWildcardContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_TypeArgWildcard(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_TypeArgWildcard(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for TypeArgWildcardContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_typeArg }
	//fn type_rule_index() -> usize where Self: Sized { RULE_typeArg }
}

impl<'input> Borrow<TypeArgContextExt<'input>> for TypeArgWildcardContext<'input>{
	fn borrow(&self) -> &TypeArgContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<TypeArgContextExt<'input>> for TypeArgWildcardContext<'input>{
	fn borrow_mut(&mut self) -> &mut TypeArgContextExt<'input> { &mut self.__base }
}

impl<'input> TypeArgContextAttrs<'input> for TypeArgWildcardContext<'input> {}

impl<'input> TypeArgWildcardContextExt<'input>{
	fn new(ctx: &dyn TypeArgContextAttrs<'input>) -> Rc<TypeArgContextAll<'input>>  {
		Rc::new(
			TypeArgContextAll::TypeArgWildcardContext(
				BaseParserRuleContext::copy_from(ctx,TypeArgWildcardContextExt{
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

impl<'input, I, H> LibSLParser<'input, I, H>
where
    I: TokenStream<'input, TF = LocalTokenFactory<'input> > + TidAble<'input>,
    H: ErrorStrategy<'input,BaseParserType<'input,I>>
{
	pub fn typeArg(&mut self,)
	-> Result<Rc<TypeArgContextAll<'input>>,ANTLRError> {
		let mut recog = self;
		let _parentctx = recog.ctx.take();
		let mut _localctx = TypeArgContextExt::new(_parentctx.clone(), recog.base.get_state());
        recog.base.enter_rule(_localctx.clone(), 156, RULE_typeArg);
        let mut _localctx: Rc<TypeArgContextAll> = _localctx;
		let mut _la: isize = -1;
		let result: Result<(), ANTLRError> = (|| {

			recog.base.set_state(1050);
			recog.err_handler.sync(&mut recog.base)?;
			match recog.base.input.la(1) {
			 L_PAREN | ASTERISK | TRUE | FALSE | NULL | IN | OUT | IMPLEMENTS | STATIC |
			 PURE | IntegerLit | FloatLit | Identifier | StringLit | CharacterLit 
				=> {
					let tmp = TypeArgTypeExprContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 1);
					_localctx = tmp;
					{
					recog.base.set_state(1046);
					recog.err_handler.sync(&mut recog.base)?;
					_la = recog.base.input.la(1);
					if _la==IN || _la==OUT {
						{
						/*InvokeRule varianceSpec*/
						recog.base.set_state(1045);
						let tmp = recog.varianceSpec()?;
						if let TypeArgContextAll::TypeArgTypeExprContext(ctx) = cast_mut::<_,TypeArgContextAll >(&mut _localctx){
						ctx.variance = Some(tmp.clone()); } else {unreachable!("cant cast");}  

						}
					}

					/*InvokeRule typeExpr*/
					recog.base.set_state(1048);
					recog.typeExpr_rec(0)?;

					}
				}

			 QUESTION 
				=> {
					let tmp = TypeArgWildcardContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 2);
					_localctx = tmp;
					{
					recog.base.set_state(1049);
					recog.base.match_token(QUESTION,&mut recog.err_handler)?;

					}
				}

				_ => Err(ANTLRError::NoAltError(NoViableAltError::new(&mut recog.base)))?
			}
			Ok(())
		})();
		match result {
		Ok(_)=>{},
        Err(e @ ANTLRError::FallThrough(_)) => return Err(e),
		Err(ref re) => {
				//_localctx.exception = re;
				recog.err_handler.report_error(&mut recog.base, re);
				recog.err_handler.recover(&mut recog.base, re)?;
			}
		}
		recog.base.exit_rule();

		Ok(_localctx)
	}
}
//------------------- block ----------------
#[derive(Debug)]
pub enum BlockContextAll<'input>{
	BlockLoneStmtContext(BlockLoneStmtContext<'input>),
	BlockBracedContext(BlockBracedContext<'input>),
Error(BlockContext<'input>)
}
antlr_rust::tid!{BlockContextAll<'a>}

impl<'input> antlr_rust::parser_rule_context::DerefSeal for BlockContextAll<'input>{}

impl<'input> LibSLParserContext<'input> for BlockContextAll<'input>{}

impl<'input> Deref for BlockContextAll<'input>{
	type Target = dyn BlockContextAttrs<'input> + 'input;
	fn deref(&self) -> &Self::Target{
		use BlockContextAll::*;
		match self{
			BlockLoneStmtContext(inner) => inner,
			BlockBracedContext(inner) => inner,
Error(inner) => inner
		}
	}
}
impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for BlockContextAll<'input>{
    fn enter(&self, listener: &mut (dyn LibSLParserListener<'input> + 'a)) { self.deref().enter(listener) }
    fn exit(&self, listener: &mut (dyn LibSLParserListener<'input> + 'a)) { self.deref().exit(listener) }
}



pub type BlockContext<'input> = BaseParserRuleContext<'input,BlockContextExt<'input>>;

#[derive(Clone)]
pub struct BlockContextExt<'input>{
ph:PhantomData<&'input str>
}

impl<'input> LibSLParserContext<'input> for BlockContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for BlockContext<'input>{
}

impl<'input> CustomRuleContext<'input> for BlockContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_block }
	//fn type_rule_index() -> usize where Self: Sized { RULE_block }
}
antlr_rust::tid!{BlockContextExt<'a>}

impl<'input> BlockContextExt<'input>{
	fn new(parent: Option<Rc<dyn LibSLParserContext<'input> + 'input > >, invoking_state: isize) -> Rc<BlockContextAll<'input>> {
		Rc::new(
		BlockContextAll::Error(
			BaseParserRuleContext::new_parser_ctx(parent, invoking_state,BlockContextExt{
				ph:PhantomData
			}),
		)
		)
	}
}

pub trait BlockContextAttrs<'input>: LibSLParserContext<'input> + BorrowMut<BlockContextExt<'input>>{


}

impl<'input> BlockContextAttrs<'input> for BlockContext<'input>{}

pub type BlockLoneStmtContext<'input> = BaseParserRuleContext<'input,BlockLoneStmtContextExt<'input>>;

pub trait BlockLoneStmtContextAttrs<'input>: LibSLParserContext<'input>{
	fn stmt(&self) -> Option<Rc<StmtContextAll<'input>>> where Self:Sized{
		self.child_of_type(0)
	}
}

impl<'input> BlockLoneStmtContextAttrs<'input> for BlockLoneStmtContext<'input>{}

pub struct BlockLoneStmtContextExt<'input>{
	__base:BlockContextExt<'input>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{BlockLoneStmtContextExt<'a>}

impl<'input> LibSLParserContext<'input> for BlockLoneStmtContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for BlockLoneStmtContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_BlockLoneStmt(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_BlockLoneStmt(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for BlockLoneStmtContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_block }
	//fn type_rule_index() -> usize where Self: Sized { RULE_block }
}

impl<'input> Borrow<BlockContextExt<'input>> for BlockLoneStmtContext<'input>{
	fn borrow(&self) -> &BlockContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<BlockContextExt<'input>> for BlockLoneStmtContext<'input>{
	fn borrow_mut(&mut self) -> &mut BlockContextExt<'input> { &mut self.__base }
}

impl<'input> BlockContextAttrs<'input> for BlockLoneStmtContext<'input> {}

impl<'input> BlockLoneStmtContextExt<'input>{
	fn new(ctx: &dyn BlockContextAttrs<'input>) -> Rc<BlockContextAll<'input>>  {
		Rc::new(
			BlockContextAll::BlockLoneStmtContext(
				BaseParserRuleContext::copy_from(ctx,BlockLoneStmtContextExt{
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type BlockBracedContext<'input> = BaseParserRuleContext<'input,BlockBracedContextExt<'input>>;

pub trait BlockBracedContextAttrs<'input>: LibSLParserContext<'input>{
	/// Retrieves first TerminalNode corresponding to token L_BRACE
	/// Returns `None` if there is no child corresponding to token L_BRACE
	fn L_BRACE(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(L_BRACE, 0)
	}
	/// Retrieves first TerminalNode corresponding to token R_BRACE
	/// Returns `None` if there is no child corresponding to token R_BRACE
	fn R_BRACE(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(R_BRACE, 0)
	}
	fn stmt_all(&self) ->  Vec<Rc<StmtContextAll<'input>>> where Self:Sized{
		self.children_of_type()
	}
	fn stmt(&self, i: usize) -> Option<Rc<StmtContextAll<'input>>> where Self:Sized{
		self.child_of_type(i)
	}
}

impl<'input> BlockBracedContextAttrs<'input> for BlockBracedContext<'input>{}

pub struct BlockBracedContextExt<'input>{
	__base:BlockContextExt<'input>,
	pub stmt: Option<Rc<StmtContextAll<'input>>>,
	pub stmts:Vec<Rc<StmtContextAll<'input>>>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{BlockBracedContextExt<'a>}

impl<'input> LibSLParserContext<'input> for BlockBracedContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for BlockBracedContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_BlockBraced(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_BlockBraced(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for BlockBracedContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_block }
	//fn type_rule_index() -> usize where Self: Sized { RULE_block }
}

impl<'input> Borrow<BlockContextExt<'input>> for BlockBracedContext<'input>{
	fn borrow(&self) -> &BlockContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<BlockContextExt<'input>> for BlockBracedContext<'input>{
	fn borrow_mut(&mut self) -> &mut BlockContextExt<'input> { &mut self.__base }
}

impl<'input> BlockContextAttrs<'input> for BlockBracedContext<'input> {}

impl<'input> BlockBracedContextExt<'input>{
	fn new(ctx: &dyn BlockContextAttrs<'input>) -> Rc<BlockContextAll<'input>>  {
		Rc::new(
			BlockContextAll::BlockBracedContext(
				BaseParserRuleContext::copy_from(ctx,BlockBracedContextExt{
        			stmt:None, 
        			stmts:Vec::new(), 
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

impl<'input, I, H> LibSLParser<'input, I, H>
where
    I: TokenStream<'input, TF = LocalTokenFactory<'input> > + TidAble<'input>,
    H: ErrorStrategy<'input,BaseParserType<'input,I>>
{
	pub fn block(&mut self,)
	-> Result<Rc<BlockContextAll<'input>>,ANTLRError> {
		let mut recog = self;
		let _parentctx = recog.ctx.take();
		let mut _localctx = BlockContextExt::new(_parentctx.clone(), recog.base.get_state());
        recog.base.enter_rule(_localctx.clone(), 158, RULE_block);
        let mut _localctx: Rc<BlockContextAll> = _localctx;
		let mut _la: isize = -1;
		let result: Result<(), ANTLRError> = (|| {

			recog.base.set_state(1061);
			recog.err_handler.sync(&mut recog.base)?;
			match  recog.interpreter.adaptive_predict(141,&mut recog.base)? {
				1 =>{
					let tmp = BlockLoneStmtContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 1);
					_localctx = tmp;
					{
					/*InvokeRule stmt*/
					recog.base.set_state(1052);
					recog.stmt()?;

					}
				}
			,
				2 =>{
					let tmp = BlockBracedContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 2);
					_localctx = tmp;
					{
					recog.base.set_state(1053);
					recog.base.match_token(L_BRACE,&mut recog.err_handler)?;

					recog.base.set_state(1057);
					recog.err_handler.sync(&mut recog.base)?;
					_la = recog.base.input.la(1);
					while (((_la) & !0x3f) == 0 && ((1usize << _la) & 68682064) != 0) || ((((_la - 35)) & !0x3f) == 0 && ((1usize << (_la - 35)) & 281018369) != 0) || ((((_la - 69)) & !0x3f) == 0 && ((1usize << (_la - 69)) & 533598385) != 0) {
						{
						{
						/*InvokeRule stmt*/
						recog.base.set_state(1054);
						let tmp = recog.stmt()?;
						if let BlockContextAll::BlockBracedContext(ctx) = cast_mut::<_,BlockContextAll >(&mut _localctx){
						ctx.stmt = Some(tmp.clone()); } else {unreachable!("cant cast");}  

						let temp = if let BlockContextAll::BlockBracedContext(ctx) = cast_mut::<_,BlockContextAll >(&mut _localctx){
						ctx.stmt.clone().unwrap() } else {unreachable!("cant cast");} ;
						if let BlockContextAll::BlockBracedContext(ctx) = cast_mut::<_,BlockContextAll >(&mut _localctx){
						ctx.stmts.push(temp); } else {unreachable!("cant cast");}  
						}
						}
						recog.base.set_state(1059);
						recog.err_handler.sync(&mut recog.base)?;
						_la = recog.base.input.la(1);
					}
					recog.base.set_state(1060);
					recog.base.match_token(R_BRACE,&mut recog.err_handler)?;

					}
				}

				_ => {}
			}
			Ok(())
		})();
		match result {
		Ok(_)=>{},
        Err(e @ ANTLRError::FallThrough(_)) => return Err(e),
		Err(ref re) => {
				//_localctx.exception = re;
				recog.err_handler.report_error(&mut recog.base, re);
				recog.err_handler.recover(&mut recog.base, re)?;
			}
		}
		recog.base.exit_rule();

		Ok(_localctx)
	}
}
//------------------- stmt ----------------
#[derive(Debug)]
pub enum StmtContextAll<'input>{
	StmtVariableDeclContext(StmtVariableDeclContext<'input>),
	StmtExprContext(StmtExprContext<'input>),
	StmtCancelContext(StmtCancelContext<'input>),
	StmtIfContext(StmtIfContext<'input>),
	StmtAssignContext(StmtAssignContext<'input>),
Error(StmtContext<'input>)
}
antlr_rust::tid!{StmtContextAll<'a>}

impl<'input> antlr_rust::parser_rule_context::DerefSeal for StmtContextAll<'input>{}

impl<'input> LibSLParserContext<'input> for StmtContextAll<'input>{}

impl<'input> Deref for StmtContextAll<'input>{
	type Target = dyn StmtContextAttrs<'input> + 'input;
	fn deref(&self) -> &Self::Target{
		use StmtContextAll::*;
		match self{
			StmtVariableDeclContext(inner) => inner,
			StmtExprContext(inner) => inner,
			StmtCancelContext(inner) => inner,
			StmtIfContext(inner) => inner,
			StmtAssignContext(inner) => inner,
Error(inner) => inner
		}
	}
}
impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for StmtContextAll<'input>{
    fn enter(&self, listener: &mut (dyn LibSLParserListener<'input> + 'a)) { self.deref().enter(listener) }
    fn exit(&self, listener: &mut (dyn LibSLParserListener<'input> + 'a)) { self.deref().exit(listener) }
}



pub type StmtContext<'input> = BaseParserRuleContext<'input,StmtContextExt<'input>>;

#[derive(Clone)]
pub struct StmtContextExt<'input>{
ph:PhantomData<&'input str>
}

impl<'input> LibSLParserContext<'input> for StmtContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for StmtContext<'input>{
}

impl<'input> CustomRuleContext<'input> for StmtContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_stmt }
	//fn type_rule_index() -> usize where Self: Sized { RULE_stmt }
}
antlr_rust::tid!{StmtContextExt<'a>}

impl<'input> StmtContextExt<'input>{
	fn new(parent: Option<Rc<dyn LibSLParserContext<'input> + 'input > >, invoking_state: isize) -> Rc<StmtContextAll<'input>> {
		Rc::new(
		StmtContextAll::Error(
			BaseParserRuleContext::new_parser_ctx(parent, invoking_state,StmtContextExt{
				ph:PhantomData
			}),
		)
		)
	}
}

pub trait StmtContextAttrs<'input>: LibSLParserContext<'input> + BorrowMut<StmtContextExt<'input>>{


}

impl<'input> StmtContextAttrs<'input> for StmtContext<'input>{}

pub type StmtVariableDeclContext<'input> = BaseParserRuleContext<'input,StmtVariableDeclContextExt<'input>>;

pub trait StmtVariableDeclContextAttrs<'input>: LibSLParserContext<'input>{
	fn variableDecl(&self) -> Option<Rc<VariableDeclContextAll<'input>>> where Self:Sized{
		self.child_of_type(0)
	}
}

impl<'input> StmtVariableDeclContextAttrs<'input> for StmtVariableDeclContext<'input>{}

pub struct StmtVariableDeclContextExt<'input>{
	__base:StmtContextExt<'input>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{StmtVariableDeclContextExt<'a>}

impl<'input> LibSLParserContext<'input> for StmtVariableDeclContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for StmtVariableDeclContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_StmtVariableDecl(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_StmtVariableDecl(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for StmtVariableDeclContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_stmt }
	//fn type_rule_index() -> usize where Self: Sized { RULE_stmt }
}

impl<'input> Borrow<StmtContextExt<'input>> for StmtVariableDeclContext<'input>{
	fn borrow(&self) -> &StmtContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<StmtContextExt<'input>> for StmtVariableDeclContext<'input>{
	fn borrow_mut(&mut self) -> &mut StmtContextExt<'input> { &mut self.__base }
}

impl<'input> StmtContextAttrs<'input> for StmtVariableDeclContext<'input> {}

impl<'input> StmtVariableDeclContextExt<'input>{
	fn new(ctx: &dyn StmtContextAttrs<'input>) -> Rc<StmtContextAll<'input>>  {
		Rc::new(
			StmtContextAll::StmtVariableDeclContext(
				BaseParserRuleContext::copy_from(ctx,StmtVariableDeclContextExt{
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type StmtExprContext<'input> = BaseParserRuleContext<'input,StmtExprContextExt<'input>>;

pub trait StmtExprContextAttrs<'input>: LibSLParserContext<'input>{
	/// Retrieves first TerminalNode corresponding to token SEMICOLON
	/// Returns `None` if there is no child corresponding to token SEMICOLON
	fn SEMICOLON(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(SEMICOLON, 0)
	}
	fn expr(&self) -> Option<Rc<ExprContextAll<'input>>> where Self:Sized{
		self.child_of_type(0)
	}
}

impl<'input> StmtExprContextAttrs<'input> for StmtExprContext<'input>{}

pub struct StmtExprContextExt<'input>{
	__base:StmtContextExt<'input>,
	pub inner: Option<Rc<ExprContextAll<'input>>>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{StmtExprContextExt<'a>}

impl<'input> LibSLParserContext<'input> for StmtExprContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for StmtExprContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_StmtExpr(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_StmtExpr(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for StmtExprContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_stmt }
	//fn type_rule_index() -> usize where Self: Sized { RULE_stmt }
}

impl<'input> Borrow<StmtContextExt<'input>> for StmtExprContext<'input>{
	fn borrow(&self) -> &StmtContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<StmtContextExt<'input>> for StmtExprContext<'input>{
	fn borrow_mut(&mut self) -> &mut StmtContextExt<'input> { &mut self.__base }
}

impl<'input> StmtContextAttrs<'input> for StmtExprContext<'input> {}

impl<'input> StmtExprContextExt<'input>{
	fn new(ctx: &dyn StmtContextAttrs<'input>) -> Rc<StmtContextAll<'input>>  {
		Rc::new(
			StmtContextAll::StmtExprContext(
				BaseParserRuleContext::copy_from(ctx,StmtExprContextExt{
        			inner:None, 
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type StmtCancelContext<'input> = BaseParserRuleContext<'input,StmtCancelContextExt<'input>>;

pub trait StmtCancelContextAttrs<'input>: LibSLParserContext<'input>{
	fn cancelStmt(&self) -> Option<Rc<CancelStmtContextAll<'input>>> where Self:Sized{
		self.child_of_type(0)
	}
}

impl<'input> StmtCancelContextAttrs<'input> for StmtCancelContext<'input>{}

pub struct StmtCancelContextExt<'input>{
	__base:StmtContextExt<'input>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{StmtCancelContextExt<'a>}

impl<'input> LibSLParserContext<'input> for StmtCancelContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for StmtCancelContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_StmtCancel(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_StmtCancel(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for StmtCancelContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_stmt }
	//fn type_rule_index() -> usize where Self: Sized { RULE_stmt }
}

impl<'input> Borrow<StmtContextExt<'input>> for StmtCancelContext<'input>{
	fn borrow(&self) -> &StmtContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<StmtContextExt<'input>> for StmtCancelContext<'input>{
	fn borrow_mut(&mut self) -> &mut StmtContextExt<'input> { &mut self.__base }
}

impl<'input> StmtContextAttrs<'input> for StmtCancelContext<'input> {}

impl<'input> StmtCancelContextExt<'input>{
	fn new(ctx: &dyn StmtContextAttrs<'input>) -> Rc<StmtContextAll<'input>>  {
		Rc::new(
			StmtContextAll::StmtCancelContext(
				BaseParserRuleContext::copy_from(ctx,StmtCancelContextExt{
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type StmtIfContext<'input> = BaseParserRuleContext<'input,StmtIfContextExt<'input>>;

pub trait StmtIfContextAttrs<'input>: LibSLParserContext<'input>{
	fn ifStmt(&self) -> Option<Rc<IfStmtContextAll<'input>>> where Self:Sized{
		self.child_of_type(0)
	}
}

impl<'input> StmtIfContextAttrs<'input> for StmtIfContext<'input>{}

pub struct StmtIfContextExt<'input>{
	__base:StmtContextExt<'input>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{StmtIfContextExt<'a>}

impl<'input> LibSLParserContext<'input> for StmtIfContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for StmtIfContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_StmtIf(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_StmtIf(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for StmtIfContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_stmt }
	//fn type_rule_index() -> usize where Self: Sized { RULE_stmt }
}

impl<'input> Borrow<StmtContextExt<'input>> for StmtIfContext<'input>{
	fn borrow(&self) -> &StmtContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<StmtContextExt<'input>> for StmtIfContext<'input>{
	fn borrow_mut(&mut self) -> &mut StmtContextExt<'input> { &mut self.__base }
}

impl<'input> StmtContextAttrs<'input> for StmtIfContext<'input> {}

impl<'input> StmtIfContextExt<'input>{
	fn new(ctx: &dyn StmtContextAttrs<'input>) -> Rc<StmtContextAll<'input>>  {
		Rc::new(
			StmtContextAll::StmtIfContext(
				BaseParserRuleContext::copy_from(ctx,StmtIfContextExt{
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type StmtAssignContext<'input> = BaseParserRuleContext<'input,StmtAssignContextExt<'input>>;

pub trait StmtAssignContextAttrs<'input>: LibSLParserContext<'input>{
	fn assignStmt(&self) -> Option<Rc<AssignStmtContextAll<'input>>> where Self:Sized{
		self.child_of_type(0)
	}
}

impl<'input> StmtAssignContextAttrs<'input> for StmtAssignContext<'input>{}

pub struct StmtAssignContextExt<'input>{
	__base:StmtContextExt<'input>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{StmtAssignContextExt<'a>}

impl<'input> LibSLParserContext<'input> for StmtAssignContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for StmtAssignContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_StmtAssign(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_StmtAssign(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for StmtAssignContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_stmt }
	//fn type_rule_index() -> usize where Self: Sized { RULE_stmt }
}

impl<'input> Borrow<StmtContextExt<'input>> for StmtAssignContext<'input>{
	fn borrow(&self) -> &StmtContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<StmtContextExt<'input>> for StmtAssignContext<'input>{
	fn borrow_mut(&mut self) -> &mut StmtContextExt<'input> { &mut self.__base }
}

impl<'input> StmtContextAttrs<'input> for StmtAssignContext<'input> {}

impl<'input> StmtAssignContextExt<'input>{
	fn new(ctx: &dyn StmtContextAttrs<'input>) -> Rc<StmtContextAll<'input>>  {
		Rc::new(
			StmtContextAll::StmtAssignContext(
				BaseParserRuleContext::copy_from(ctx,StmtAssignContextExt{
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

impl<'input, I, H> LibSLParser<'input, I, H>
where
    I: TokenStream<'input, TF = LocalTokenFactory<'input> > + TidAble<'input>,
    H: ErrorStrategy<'input,BaseParserType<'input,I>>
{
	pub fn stmt(&mut self,)
	-> Result<Rc<StmtContextAll<'input>>,ANTLRError> {
		let mut recog = self;
		let _parentctx = recog.ctx.take();
		let mut _localctx = StmtContextExt::new(_parentctx.clone(), recog.base.get_state());
        recog.base.enter_rule(_localctx.clone(), 160, RULE_stmt);
        let mut _localctx: Rc<StmtContextAll> = _localctx;
		let result: Result<(), ANTLRError> = (|| {

			recog.base.set_state(1070);
			recog.err_handler.sync(&mut recog.base)?;
			match  recog.interpreter.adaptive_predict(142,&mut recog.base)? {
				1 =>{
					let tmp = StmtVariableDeclContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 1);
					_localctx = tmp;
					{
					/*InvokeRule variableDecl*/
					recog.base.set_state(1063);
					recog.variableDecl()?;

					}
				}
			,
				2 =>{
					let tmp = StmtIfContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 2);
					_localctx = tmp;
					{
					/*InvokeRule ifStmt*/
					recog.base.set_state(1064);
					recog.ifStmt()?;

					}
				}
			,
				3 =>{
					let tmp = StmtAssignContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 3);
					_localctx = tmp;
					{
					/*InvokeRule assignStmt*/
					recog.base.set_state(1065);
					recog.assignStmt()?;

					}
				}
			,
				4 =>{
					let tmp = StmtCancelContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 4);
					_localctx = tmp;
					{
					/*InvokeRule cancelStmt*/
					recog.base.set_state(1066);
					recog.cancelStmt()?;

					}
				}
			,
				5 =>{
					let tmp = StmtExprContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 5);
					_localctx = tmp;
					{
					/*InvokeRule expr*/
					recog.base.set_state(1067);
					let tmp = recog.expr_rec(0)?;
					if let StmtContextAll::StmtExprContext(ctx) = cast_mut::<_,StmtContextAll >(&mut _localctx){
					ctx.inner = Some(tmp.clone()); } else {unreachable!("cant cast");}  

					recog.base.set_state(1068);
					recog.base.match_token(SEMICOLON,&mut recog.err_handler)?;

					}
				}

				_ => {}
			}
			Ok(())
		})();
		match result {
		Ok(_)=>{},
        Err(e @ ANTLRError::FallThrough(_)) => return Err(e),
		Err(ref re) => {
				//_localctx.exception = re;
				recog.err_handler.report_error(&mut recog.base, re);
				recog.err_handler.recover(&mut recog.base, re)?;
			}
		}
		recog.base.exit_rule();

		Ok(_localctx)
	}
}
//------------------- ifStmt ----------------
pub type IfStmtContextAll<'input> = IfStmtContext<'input>;


pub type IfStmtContext<'input> = BaseParserRuleContext<'input,IfStmtContextExt<'input>>;

#[derive(Clone)]
pub struct IfStmtContextExt<'input>{
	pub condition: Option<Rc<ExprContextAll<'input>>>,
	pub thenBranch: Option<Rc<BlockContextAll<'input>>>,
	pub elseBranch: Option<Rc<BlockContextAll<'input>>>,
ph:PhantomData<&'input str>
}

impl<'input> LibSLParserContext<'input> for IfStmtContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for IfStmtContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_ifStmt(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_ifStmt(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for IfStmtContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_ifStmt }
	//fn type_rule_index() -> usize where Self: Sized { RULE_ifStmt }
}
antlr_rust::tid!{IfStmtContextExt<'a>}

impl<'input> IfStmtContextExt<'input>{
	fn new(parent: Option<Rc<dyn LibSLParserContext<'input> + 'input > >, invoking_state: isize) -> Rc<IfStmtContextAll<'input>> {
		Rc::new(
			BaseParserRuleContext::new_parser_ctx(parent, invoking_state,IfStmtContextExt{
				condition: None, thenBranch: None, elseBranch: None, 
				ph:PhantomData
			}),
		)
	}
}

pub trait IfStmtContextAttrs<'input>: LibSLParserContext<'input> + BorrowMut<IfStmtContextExt<'input>>{

/// Retrieves first TerminalNode corresponding to token IF
/// Returns `None` if there is no child corresponding to token IF
fn IF(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(IF, 0)
}
/// Retrieves first TerminalNode corresponding to token L_PAREN
/// Returns `None` if there is no child corresponding to token L_PAREN
fn L_PAREN(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(L_PAREN, 0)
}
/// Retrieves first TerminalNode corresponding to token R_PAREN
/// Returns `None` if there is no child corresponding to token R_PAREN
fn R_PAREN(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(R_PAREN, 0)
}
fn expr(&self) -> Option<Rc<ExprContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}
fn block_all(&self) ->  Vec<Rc<BlockContextAll<'input>>> where Self:Sized{
	self.children_of_type()
}
fn block(&self, i: usize) -> Option<Rc<BlockContextAll<'input>>> where Self:Sized{
	self.child_of_type(i)
}
/// Retrieves first TerminalNode corresponding to token ELSE
/// Returns `None` if there is no child corresponding to token ELSE
fn ELSE(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(ELSE, 0)
}

}

impl<'input> IfStmtContextAttrs<'input> for IfStmtContext<'input>{}

impl<'input, I, H> LibSLParser<'input, I, H>
where
    I: TokenStream<'input, TF = LocalTokenFactory<'input> > + TidAble<'input>,
    H: ErrorStrategy<'input,BaseParserType<'input,I>>
{
	pub fn ifStmt(&mut self,)
	-> Result<Rc<IfStmtContextAll<'input>>,ANTLRError> {
		let mut recog = self;
		let _parentctx = recog.ctx.take();
		let mut _localctx = IfStmtContextExt::new(_parentctx.clone(), recog.base.get_state());
        recog.base.enter_rule(_localctx.clone(), 162, RULE_ifStmt);
        let mut _localctx: Rc<IfStmtContextAll> = _localctx;
		let result: Result<(), ANTLRError> = (|| {

			//recog.base.enter_outer_alt(_localctx.clone(), 1);
			recog.base.enter_outer_alt(None, 1);
			{
			recog.base.set_state(1072);
			recog.base.match_token(IF,&mut recog.err_handler)?;

			recog.base.set_state(1073);
			recog.base.match_token(L_PAREN,&mut recog.err_handler)?;

			/*InvokeRule expr*/
			recog.base.set_state(1074);
			let tmp = recog.expr_rec(0)?;
			 cast_mut::<_,IfStmtContext >(&mut _localctx).condition = Some(tmp.clone());
			  

			recog.base.set_state(1075);
			recog.base.match_token(R_PAREN,&mut recog.err_handler)?;

			/*InvokeRule block*/
			recog.base.set_state(1076);
			let tmp = recog.block()?;
			 cast_mut::<_,IfStmtContext >(&mut _localctx).thenBranch = Some(tmp.clone());
			  

			recog.base.set_state(1079);
			recog.err_handler.sync(&mut recog.base)?;
			match  recog.interpreter.adaptive_predict(143,&mut recog.base)? {
				x if x == 1=>{
					{
					recog.base.set_state(1077);
					recog.base.match_token(ELSE,&mut recog.err_handler)?;

					/*InvokeRule block*/
					recog.base.set_state(1078);
					let tmp = recog.block()?;
					 cast_mut::<_,IfStmtContext >(&mut _localctx).elseBranch = Some(tmp.clone());
					  

					}
				}

				_ => {}
			}
			}
			Ok(())
		})();
		match result {
		Ok(_)=>{},
        Err(e @ ANTLRError::FallThrough(_)) => return Err(e),
		Err(ref re) => {
				//_localctx.exception = re;
				recog.err_handler.report_error(&mut recog.base, re);
				recog.err_handler.recover(&mut recog.base, re)?;
			}
		}
		recog.base.exit_rule();

		Ok(_localctx)
	}
}
//------------------- assignStmt ----------------
pub type AssignStmtContextAll<'input> = AssignStmtContext<'input>;


pub type AssignStmtContext<'input> = BaseParserRuleContext<'input,AssignStmtContextExt<'input>>;

#[derive(Clone)]
pub struct AssignStmtContextExt<'input>{
	pub lhs: Option<Rc<AssigneeContextAll<'input>>>,
	pub op: Option<Rc<AssignOpContextAll<'input>>>,
	pub rhs: Option<Rc<ExprContextAll<'input>>>,
ph:PhantomData<&'input str>
}

impl<'input> LibSLParserContext<'input> for AssignStmtContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for AssignStmtContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_assignStmt(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_assignStmt(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for AssignStmtContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_assignStmt }
	//fn type_rule_index() -> usize where Self: Sized { RULE_assignStmt }
}
antlr_rust::tid!{AssignStmtContextExt<'a>}

impl<'input> AssignStmtContextExt<'input>{
	fn new(parent: Option<Rc<dyn LibSLParserContext<'input> + 'input > >, invoking_state: isize) -> Rc<AssignStmtContextAll<'input>> {
		Rc::new(
			BaseParserRuleContext::new_parser_ctx(parent, invoking_state,AssignStmtContextExt{
				lhs: None, op: None, rhs: None, 
				ph:PhantomData
			}),
		)
	}
}

pub trait AssignStmtContextAttrs<'input>: LibSLParserContext<'input> + BorrowMut<AssignStmtContextExt<'input>>{

/// Retrieves first TerminalNode corresponding to token SEMICOLON
/// Returns `None` if there is no child corresponding to token SEMICOLON
fn SEMICOLON(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(SEMICOLON, 0)
}
fn assignee(&self) -> Option<Rc<AssigneeContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}
fn assignOp(&self) -> Option<Rc<AssignOpContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}
fn expr(&self) -> Option<Rc<ExprContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}

}

impl<'input> AssignStmtContextAttrs<'input> for AssignStmtContext<'input>{}

impl<'input, I, H> LibSLParser<'input, I, H>
where
    I: TokenStream<'input, TF = LocalTokenFactory<'input> > + TidAble<'input>,
    H: ErrorStrategy<'input,BaseParserType<'input,I>>
{
	pub fn assignStmt(&mut self,)
	-> Result<Rc<AssignStmtContextAll<'input>>,ANTLRError> {
		let mut recog = self;
		let _parentctx = recog.ctx.take();
		let mut _localctx = AssignStmtContextExt::new(_parentctx.clone(), recog.base.get_state());
        recog.base.enter_rule(_localctx.clone(), 164, RULE_assignStmt);
        let mut _localctx: Rc<AssignStmtContextAll> = _localctx;
		let result: Result<(), ANTLRError> = (|| {

			//recog.base.enter_outer_alt(_localctx.clone(), 1);
			recog.base.enter_outer_alt(None, 1);
			{
			/*InvokeRule assignee*/
			recog.base.set_state(1081);
			let tmp = recog.assignee()?;
			 cast_mut::<_,AssignStmtContext >(&mut _localctx).lhs = Some(tmp.clone());
			  

			/*InvokeRule assignOp*/
			recog.base.set_state(1082);
			let tmp = recog.assignOp()?;
			 cast_mut::<_,AssignStmtContext >(&mut _localctx).op = Some(tmp.clone());
			  

			/*InvokeRule expr*/
			recog.base.set_state(1083);
			let tmp = recog.expr_rec(0)?;
			 cast_mut::<_,AssignStmtContext >(&mut _localctx).rhs = Some(tmp.clone());
			  

			recog.base.set_state(1084);
			recog.base.match_token(SEMICOLON,&mut recog.err_handler)?;

			}
			Ok(())
		})();
		match result {
		Ok(_)=>{},
        Err(e @ ANTLRError::FallThrough(_)) => return Err(e),
		Err(ref re) => {
				//_localctx.exception = re;
				recog.err_handler.report_error(&mut recog.base, re);
				recog.err_handler.recover(&mut recog.base, re)?;
			}
		}
		recog.base.exit_rule();

		Ok(_localctx)
	}
}
//------------------- assignee ----------------
#[derive(Debug)]
pub enum AssigneeContextAll<'input>{
	AssigneeNameContext(AssigneeNameContext<'input>),
	AssigneeFieldContext(AssigneeFieldContext<'input>),
	AssigneeIndexContext(AssigneeIndexContext<'input>),
Error(AssigneeContext<'input>)
}
antlr_rust::tid!{AssigneeContextAll<'a>}

impl<'input> antlr_rust::parser_rule_context::DerefSeal for AssigneeContextAll<'input>{}

impl<'input> LibSLParserContext<'input> for AssigneeContextAll<'input>{}

impl<'input> Deref for AssigneeContextAll<'input>{
	type Target = dyn AssigneeContextAttrs<'input> + 'input;
	fn deref(&self) -> &Self::Target{
		use AssigneeContextAll::*;
		match self{
			AssigneeNameContext(inner) => inner,
			AssigneeFieldContext(inner) => inner,
			AssigneeIndexContext(inner) => inner,
Error(inner) => inner
		}
	}
}
impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for AssigneeContextAll<'input>{
    fn enter(&self, listener: &mut (dyn LibSLParserListener<'input> + 'a)) { self.deref().enter(listener) }
    fn exit(&self, listener: &mut (dyn LibSLParserListener<'input> + 'a)) { self.deref().exit(listener) }
}



pub type AssigneeContext<'input> = BaseParserRuleContext<'input,AssigneeContextExt<'input>>;

#[derive(Clone)]
pub struct AssigneeContextExt<'input>{
ph:PhantomData<&'input str>
}

impl<'input> LibSLParserContext<'input> for AssigneeContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for AssigneeContext<'input>{
}

impl<'input> CustomRuleContext<'input> for AssigneeContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_assignee }
	//fn type_rule_index() -> usize where Self: Sized { RULE_assignee }
}
antlr_rust::tid!{AssigneeContextExt<'a>}

impl<'input> AssigneeContextExt<'input>{
	fn new(parent: Option<Rc<dyn LibSLParserContext<'input> + 'input > >, invoking_state: isize) -> Rc<AssigneeContextAll<'input>> {
		Rc::new(
		AssigneeContextAll::Error(
			BaseParserRuleContext::new_parser_ctx(parent, invoking_state,AssigneeContextExt{
				ph:PhantomData
			}),
		)
		)
	}
}

pub trait AssigneeContextAttrs<'input>: LibSLParserContext<'input> + BorrowMut<AssigneeContextExt<'input>>{


}

impl<'input> AssigneeContextAttrs<'input> for AssigneeContext<'input>{}

pub type AssigneeNameContext<'input> = BaseParserRuleContext<'input,AssigneeNameContextExt<'input>>;

pub trait AssigneeNameContextAttrs<'input>: LibSLParserContext<'input>{
	fn ident(&self) -> Option<Rc<IdentContextAll<'input>>> where Self:Sized{
		self.child_of_type(0)
	}
}

impl<'input> AssigneeNameContextAttrs<'input> for AssigneeNameContext<'input>{}

pub struct AssigneeNameContextExt<'input>{
	__base:AssigneeContextExt<'input>,
	pub name: Option<Rc<IdentContextAll<'input>>>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{AssigneeNameContextExt<'a>}

impl<'input> LibSLParserContext<'input> for AssigneeNameContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for AssigneeNameContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_AssigneeName(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_AssigneeName(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for AssigneeNameContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_assignee }
	//fn type_rule_index() -> usize where Self: Sized { RULE_assignee }
}

impl<'input> Borrow<AssigneeContextExt<'input>> for AssigneeNameContext<'input>{
	fn borrow(&self) -> &AssigneeContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<AssigneeContextExt<'input>> for AssigneeNameContext<'input>{
	fn borrow_mut(&mut self) -> &mut AssigneeContextExt<'input> { &mut self.__base }
}

impl<'input> AssigneeContextAttrs<'input> for AssigneeNameContext<'input> {}

impl<'input> AssigneeNameContextExt<'input>{
	fn new(ctx: &dyn AssigneeContextAttrs<'input>) -> Rc<AssigneeContextAll<'input>>  {
		Rc::new(
			AssigneeContextAll::AssigneeNameContext(
				BaseParserRuleContext::copy_from(ctx,AssigneeNameContextExt{
        			name:None, 
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type AssigneeFieldContext<'input> = BaseParserRuleContext<'input,AssigneeFieldContextExt<'input>>;

pub trait AssigneeFieldContextAttrs<'input>: LibSLParserContext<'input>{
	/// Retrieves first TerminalNode corresponding to token DOT
	/// Returns `None` if there is no child corresponding to token DOT
	fn DOT(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(DOT, 0)
	}
	fn expr(&self) -> Option<Rc<ExprContextAll<'input>>> where Self:Sized{
		self.child_of_type(0)
	}
	fn ident(&self) -> Option<Rc<IdentContextAll<'input>>> where Self:Sized{
		self.child_of_type(0)
	}
}

impl<'input> AssigneeFieldContextAttrs<'input> for AssigneeFieldContext<'input>{}

pub struct AssigneeFieldContextExt<'input>{
	__base:AssigneeContextExt<'input>,
	pub base: Option<Rc<ExprContextAll<'input>>>,
	pub field: Option<Rc<IdentContextAll<'input>>>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{AssigneeFieldContextExt<'a>}

impl<'input> LibSLParserContext<'input> for AssigneeFieldContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for AssigneeFieldContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_AssigneeField(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_AssigneeField(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for AssigneeFieldContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_assignee }
	//fn type_rule_index() -> usize where Self: Sized { RULE_assignee }
}

impl<'input> Borrow<AssigneeContextExt<'input>> for AssigneeFieldContext<'input>{
	fn borrow(&self) -> &AssigneeContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<AssigneeContextExt<'input>> for AssigneeFieldContext<'input>{
	fn borrow_mut(&mut self) -> &mut AssigneeContextExt<'input> { &mut self.__base }
}

impl<'input> AssigneeContextAttrs<'input> for AssigneeFieldContext<'input> {}

impl<'input> AssigneeFieldContextExt<'input>{
	fn new(ctx: &dyn AssigneeContextAttrs<'input>) -> Rc<AssigneeContextAll<'input>>  {
		Rc::new(
			AssigneeContextAll::AssigneeFieldContext(
				BaseParserRuleContext::copy_from(ctx,AssigneeFieldContextExt{
        			base:None, field:None, 
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type AssigneeIndexContext<'input> = BaseParserRuleContext<'input,AssigneeIndexContextExt<'input>>;

pub trait AssigneeIndexContextAttrs<'input>: LibSLParserContext<'input>{
	/// Retrieves first TerminalNode corresponding to token L_BRACKET
	/// Returns `None` if there is no child corresponding to token L_BRACKET
	fn L_BRACKET(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(L_BRACKET, 0)
	}
	/// Retrieves first TerminalNode corresponding to token R_BRACKET
	/// Returns `None` if there is no child corresponding to token R_BRACKET
	fn R_BRACKET(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(R_BRACKET, 0)
	}
	fn expr_all(&self) ->  Vec<Rc<ExprContextAll<'input>>> where Self:Sized{
		self.children_of_type()
	}
	fn expr(&self, i: usize) -> Option<Rc<ExprContextAll<'input>>> where Self:Sized{
		self.child_of_type(i)
	}
}

impl<'input> AssigneeIndexContextAttrs<'input> for AssigneeIndexContext<'input>{}

pub struct AssigneeIndexContextExt<'input>{
	__base:AssigneeContextExt<'input>,
	pub base: Option<Rc<ExprContextAll<'input>>>,
	pub index: Option<Rc<ExprContextAll<'input>>>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{AssigneeIndexContextExt<'a>}

impl<'input> LibSLParserContext<'input> for AssigneeIndexContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for AssigneeIndexContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_AssigneeIndex(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_AssigneeIndex(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for AssigneeIndexContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_assignee }
	//fn type_rule_index() -> usize where Self: Sized { RULE_assignee }
}

impl<'input> Borrow<AssigneeContextExt<'input>> for AssigneeIndexContext<'input>{
	fn borrow(&self) -> &AssigneeContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<AssigneeContextExt<'input>> for AssigneeIndexContext<'input>{
	fn borrow_mut(&mut self) -> &mut AssigneeContextExt<'input> { &mut self.__base }
}

impl<'input> AssigneeContextAttrs<'input> for AssigneeIndexContext<'input> {}

impl<'input> AssigneeIndexContextExt<'input>{
	fn new(ctx: &dyn AssigneeContextAttrs<'input>) -> Rc<AssigneeContextAll<'input>>  {
		Rc::new(
			AssigneeContextAll::AssigneeIndexContext(
				BaseParserRuleContext::copy_from(ctx,AssigneeIndexContextExt{
        			base:None, index:None, 
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

impl<'input, I, H> LibSLParser<'input, I, H>
where
    I: TokenStream<'input, TF = LocalTokenFactory<'input> > + TidAble<'input>,
    H: ErrorStrategy<'input,BaseParserType<'input,I>>
{
	pub fn assignee(&mut self,)
	-> Result<Rc<AssigneeContextAll<'input>>,ANTLRError> {
		let mut recog = self;
		let _parentctx = recog.ctx.take();
		let mut _localctx = AssigneeContextExt::new(_parentctx.clone(), recog.base.get_state());
        recog.base.enter_rule(_localctx.clone(), 166, RULE_assignee);
        let mut _localctx: Rc<AssigneeContextAll> = _localctx;
		let result: Result<(), ANTLRError> = (|| {

			recog.base.set_state(1096);
			recog.err_handler.sync(&mut recog.base)?;
			match  recog.interpreter.adaptive_predict(144,&mut recog.base)? {
				1 =>{
					let tmp = AssigneeNameContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 1);
					_localctx = tmp;
					{
					/*InvokeRule ident*/
					recog.base.set_state(1086);
					let tmp = recog.ident()?;
					if let AssigneeContextAll::AssigneeNameContext(ctx) = cast_mut::<_,AssigneeContextAll >(&mut _localctx){
					ctx.name = Some(tmp.clone()); } else {unreachable!("cant cast");}  

					}
				}
			,
				2 =>{
					let tmp = AssigneeFieldContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 2);
					_localctx = tmp;
					{
					/*InvokeRule expr*/
					recog.base.set_state(1087);
					let tmp = recog.expr_rec(0)?;
					if let AssigneeContextAll::AssigneeFieldContext(ctx) = cast_mut::<_,AssigneeContextAll >(&mut _localctx){
					ctx.base = Some(tmp.clone()); } else {unreachable!("cant cast");}  

					recog.base.set_state(1088);
					recog.base.match_token(DOT,&mut recog.err_handler)?;

					/*InvokeRule ident*/
					recog.base.set_state(1089);
					let tmp = recog.ident()?;
					if let AssigneeContextAll::AssigneeFieldContext(ctx) = cast_mut::<_,AssigneeContextAll >(&mut _localctx){
					ctx.field = Some(tmp.clone()); } else {unreachable!("cant cast");}  

					}
				}
			,
				3 =>{
					let tmp = AssigneeIndexContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 3);
					_localctx = tmp;
					{
					/*InvokeRule expr*/
					recog.base.set_state(1091);
					let tmp = recog.expr_rec(0)?;
					if let AssigneeContextAll::AssigneeIndexContext(ctx) = cast_mut::<_,AssigneeContextAll >(&mut _localctx){
					ctx.base = Some(tmp.clone()); } else {unreachable!("cant cast");}  

					recog.base.set_state(1092);
					recog.base.match_token(L_BRACKET,&mut recog.err_handler)?;

					/*InvokeRule expr*/
					recog.base.set_state(1093);
					let tmp = recog.expr_rec(0)?;
					if let AssigneeContextAll::AssigneeIndexContext(ctx) = cast_mut::<_,AssigneeContextAll >(&mut _localctx){
					ctx.index = Some(tmp.clone()); } else {unreachable!("cant cast");}  

					recog.base.set_state(1094);
					recog.base.match_token(R_BRACKET,&mut recog.err_handler)?;

					}
				}

				_ => {}
			}
			Ok(())
		})();
		match result {
		Ok(_)=>{},
        Err(e @ ANTLRError::FallThrough(_)) => return Err(e),
		Err(ref re) => {
				//_localctx.exception = re;
				recog.err_handler.report_error(&mut recog.base, re);
				recog.err_handler.recover(&mut recog.base, re)?;
			}
		}
		recog.base.exit_rule();

		Ok(_localctx)
	}
}
//------------------- cancelStmt ----------------
pub type CancelStmtContextAll<'input> = CancelStmtContext<'input>;


pub type CancelStmtContext<'input> = BaseParserRuleContext<'input,CancelStmtContextExt<'input>>;

#[derive(Clone)]
pub struct CancelStmtContextExt<'input>{
ph:PhantomData<&'input str>
}

impl<'input> LibSLParserContext<'input> for CancelStmtContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for CancelStmtContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_cancelStmt(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_cancelStmt(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for CancelStmtContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_cancelStmt }
	//fn type_rule_index() -> usize where Self: Sized { RULE_cancelStmt }
}
antlr_rust::tid!{CancelStmtContextExt<'a>}

impl<'input> CancelStmtContextExt<'input>{
	fn new(parent: Option<Rc<dyn LibSLParserContext<'input> + 'input > >, invoking_state: isize) -> Rc<CancelStmtContextAll<'input>> {
		Rc::new(
			BaseParserRuleContext::new_parser_ctx(parent, invoking_state,CancelStmtContextExt{
				ph:PhantomData
			}),
		)
	}
}

pub trait CancelStmtContextAttrs<'input>: LibSLParserContext<'input> + BorrowMut<CancelStmtContextExt<'input>>{

/// Retrieves first TerminalNode corresponding to token CANCEL
/// Returns `None` if there is no child corresponding to token CANCEL
fn CANCEL(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(CANCEL, 0)
}
/// Retrieves first TerminalNode corresponding to token SEMICOLON
/// Returns `None` if there is no child corresponding to token SEMICOLON
fn SEMICOLON(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(SEMICOLON, 0)
}

}

impl<'input> CancelStmtContextAttrs<'input> for CancelStmtContext<'input>{}

impl<'input, I, H> LibSLParser<'input, I, H>
where
    I: TokenStream<'input, TF = LocalTokenFactory<'input> > + TidAble<'input>,
    H: ErrorStrategy<'input,BaseParserType<'input,I>>
{
	pub fn cancelStmt(&mut self,)
	-> Result<Rc<CancelStmtContextAll<'input>>,ANTLRError> {
		let mut recog = self;
		let _parentctx = recog.ctx.take();
		let mut _localctx = CancelStmtContextExt::new(_parentctx.clone(), recog.base.get_state());
        recog.base.enter_rule(_localctx.clone(), 168, RULE_cancelStmt);
        let mut _localctx: Rc<CancelStmtContextAll> = _localctx;
		let result: Result<(), ANTLRError> = (|| {

			//recog.base.enter_outer_alt(_localctx.clone(), 1);
			recog.base.enter_outer_alt(None, 1);
			{
			recog.base.set_state(1098);
			recog.base.match_token(CANCEL,&mut recog.err_handler)?;

			recog.base.set_state(1099);
			recog.base.match_token(SEMICOLON,&mut recog.err_handler)?;

			}
			Ok(())
		})();
		match result {
		Ok(_)=>{},
        Err(e @ ANTLRError::FallThrough(_)) => return Err(e),
		Err(ref re) => {
				//_localctx.exception = re;
				recog.err_handler.report_error(&mut recog.base, re);
				recog.err_handler.recover(&mut recog.base, re)?;
			}
		}
		recog.base.exit_rule();

		Ok(_localctx)
	}
}
//------------------- assignOp ----------------
#[derive(Debug)]
pub enum AssignOpContextAll<'input>{
	OpAddAssignContext(OpAddAssignContext<'input>),
	OpModAssignContext(OpModAssignContext<'input>),
	OpBitAndAssignContext(OpBitAndAssignContext<'input>),
	OpBitXorAssignContext(OpBitXorAssignContext<'input>),
	OpSubAssignContext(OpSubAssignContext<'input>),
	OpLShiftAssignContext(OpLShiftAssignContext<'input>),
	OpRShiftAssignContext(OpRShiftAssignContext<'input>),
	OpBitOrAssignContext(OpBitOrAssignContext<'input>),
	OpMulAssignContext(OpMulAssignContext<'input>),
	OpAssignContext(OpAssignContext<'input>),
	OpDivAssignContext(OpDivAssignContext<'input>),
Error(AssignOpContext<'input>)
}
antlr_rust::tid!{AssignOpContextAll<'a>}

impl<'input> antlr_rust::parser_rule_context::DerefSeal for AssignOpContextAll<'input>{}

impl<'input> LibSLParserContext<'input> for AssignOpContextAll<'input>{}

impl<'input> Deref for AssignOpContextAll<'input>{
	type Target = dyn AssignOpContextAttrs<'input> + 'input;
	fn deref(&self) -> &Self::Target{
		use AssignOpContextAll::*;
		match self{
			OpAddAssignContext(inner) => inner,
			OpModAssignContext(inner) => inner,
			OpBitAndAssignContext(inner) => inner,
			OpBitXorAssignContext(inner) => inner,
			OpSubAssignContext(inner) => inner,
			OpLShiftAssignContext(inner) => inner,
			OpRShiftAssignContext(inner) => inner,
			OpBitOrAssignContext(inner) => inner,
			OpMulAssignContext(inner) => inner,
			OpAssignContext(inner) => inner,
			OpDivAssignContext(inner) => inner,
Error(inner) => inner
		}
	}
}
impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for AssignOpContextAll<'input>{
    fn enter(&self, listener: &mut (dyn LibSLParserListener<'input> + 'a)) { self.deref().enter(listener) }
    fn exit(&self, listener: &mut (dyn LibSLParserListener<'input> + 'a)) { self.deref().exit(listener) }
}



pub type AssignOpContext<'input> = BaseParserRuleContext<'input,AssignOpContextExt<'input>>;

#[derive(Clone)]
pub struct AssignOpContextExt<'input>{
ph:PhantomData<&'input str>
}

impl<'input> LibSLParserContext<'input> for AssignOpContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for AssignOpContext<'input>{
}

impl<'input> CustomRuleContext<'input> for AssignOpContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_assignOp }
	//fn type_rule_index() -> usize where Self: Sized { RULE_assignOp }
}
antlr_rust::tid!{AssignOpContextExt<'a>}

impl<'input> AssignOpContextExt<'input>{
	fn new(parent: Option<Rc<dyn LibSLParserContext<'input> + 'input > >, invoking_state: isize) -> Rc<AssignOpContextAll<'input>> {
		Rc::new(
		AssignOpContextAll::Error(
			BaseParserRuleContext::new_parser_ctx(parent, invoking_state,AssignOpContextExt{
				ph:PhantomData
			}),
		)
		)
	}
}

pub trait AssignOpContextAttrs<'input>: LibSLParserContext<'input> + BorrowMut<AssignOpContextExt<'input>>{


}

impl<'input> AssignOpContextAttrs<'input> for AssignOpContext<'input>{}

pub type OpAddAssignContext<'input> = BaseParserRuleContext<'input,OpAddAssignContextExt<'input>>;

pub trait OpAddAssignContextAttrs<'input>: LibSLParserContext<'input>{
	/// Retrieves first TerminalNode corresponding to token PLUS_EQ
	/// Returns `None` if there is no child corresponding to token PLUS_EQ
	fn PLUS_EQ(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(PLUS_EQ, 0)
	}
}

impl<'input> OpAddAssignContextAttrs<'input> for OpAddAssignContext<'input>{}

pub struct OpAddAssignContextExt<'input>{
	__base:AssignOpContextExt<'input>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{OpAddAssignContextExt<'a>}

impl<'input> LibSLParserContext<'input> for OpAddAssignContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for OpAddAssignContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_OpAddAssign(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_OpAddAssign(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for OpAddAssignContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_assignOp }
	//fn type_rule_index() -> usize where Self: Sized { RULE_assignOp }
}

impl<'input> Borrow<AssignOpContextExt<'input>> for OpAddAssignContext<'input>{
	fn borrow(&self) -> &AssignOpContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<AssignOpContextExt<'input>> for OpAddAssignContext<'input>{
	fn borrow_mut(&mut self) -> &mut AssignOpContextExt<'input> { &mut self.__base }
}

impl<'input> AssignOpContextAttrs<'input> for OpAddAssignContext<'input> {}

impl<'input> OpAddAssignContextExt<'input>{
	fn new(ctx: &dyn AssignOpContextAttrs<'input>) -> Rc<AssignOpContextAll<'input>>  {
		Rc::new(
			AssignOpContextAll::OpAddAssignContext(
				BaseParserRuleContext::copy_from(ctx,OpAddAssignContextExt{
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type OpModAssignContext<'input> = BaseParserRuleContext<'input,OpModAssignContextExt<'input>>;

pub trait OpModAssignContextAttrs<'input>: LibSLParserContext<'input>{
	/// Retrieves first TerminalNode corresponding to token PERCENT_EQ
	/// Returns `None` if there is no child corresponding to token PERCENT_EQ
	fn PERCENT_EQ(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(PERCENT_EQ, 0)
	}
}

impl<'input> OpModAssignContextAttrs<'input> for OpModAssignContext<'input>{}

pub struct OpModAssignContextExt<'input>{
	__base:AssignOpContextExt<'input>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{OpModAssignContextExt<'a>}

impl<'input> LibSLParserContext<'input> for OpModAssignContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for OpModAssignContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_OpModAssign(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_OpModAssign(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for OpModAssignContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_assignOp }
	//fn type_rule_index() -> usize where Self: Sized { RULE_assignOp }
}

impl<'input> Borrow<AssignOpContextExt<'input>> for OpModAssignContext<'input>{
	fn borrow(&self) -> &AssignOpContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<AssignOpContextExt<'input>> for OpModAssignContext<'input>{
	fn borrow_mut(&mut self) -> &mut AssignOpContextExt<'input> { &mut self.__base }
}

impl<'input> AssignOpContextAttrs<'input> for OpModAssignContext<'input> {}

impl<'input> OpModAssignContextExt<'input>{
	fn new(ctx: &dyn AssignOpContextAttrs<'input>) -> Rc<AssignOpContextAll<'input>>  {
		Rc::new(
			AssignOpContextAll::OpModAssignContext(
				BaseParserRuleContext::copy_from(ctx,OpModAssignContextExt{
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type OpBitAndAssignContext<'input> = BaseParserRuleContext<'input,OpBitAndAssignContextExt<'input>>;

pub trait OpBitAndAssignContextAttrs<'input>: LibSLParserContext<'input>{
	/// Retrieves first TerminalNode corresponding to token AMP_EQ
	/// Returns `None` if there is no child corresponding to token AMP_EQ
	fn AMP_EQ(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(AMP_EQ, 0)
	}
}

impl<'input> OpBitAndAssignContextAttrs<'input> for OpBitAndAssignContext<'input>{}

pub struct OpBitAndAssignContextExt<'input>{
	__base:AssignOpContextExt<'input>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{OpBitAndAssignContextExt<'a>}

impl<'input> LibSLParserContext<'input> for OpBitAndAssignContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for OpBitAndAssignContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_OpBitAndAssign(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_OpBitAndAssign(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for OpBitAndAssignContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_assignOp }
	//fn type_rule_index() -> usize where Self: Sized { RULE_assignOp }
}

impl<'input> Borrow<AssignOpContextExt<'input>> for OpBitAndAssignContext<'input>{
	fn borrow(&self) -> &AssignOpContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<AssignOpContextExt<'input>> for OpBitAndAssignContext<'input>{
	fn borrow_mut(&mut self) -> &mut AssignOpContextExt<'input> { &mut self.__base }
}

impl<'input> AssignOpContextAttrs<'input> for OpBitAndAssignContext<'input> {}

impl<'input> OpBitAndAssignContextExt<'input>{
	fn new(ctx: &dyn AssignOpContextAttrs<'input>) -> Rc<AssignOpContextAll<'input>>  {
		Rc::new(
			AssignOpContextAll::OpBitAndAssignContext(
				BaseParserRuleContext::copy_from(ctx,OpBitAndAssignContextExt{
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type OpBitXorAssignContext<'input> = BaseParserRuleContext<'input,OpBitXorAssignContextExt<'input>>;

pub trait OpBitXorAssignContextAttrs<'input>: LibSLParserContext<'input>{
	/// Retrieves first TerminalNode corresponding to token CARET_EQ
	/// Returns `None` if there is no child corresponding to token CARET_EQ
	fn CARET_EQ(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(CARET_EQ, 0)
	}
}

impl<'input> OpBitXorAssignContextAttrs<'input> for OpBitXorAssignContext<'input>{}

pub struct OpBitXorAssignContextExt<'input>{
	__base:AssignOpContextExt<'input>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{OpBitXorAssignContextExt<'a>}

impl<'input> LibSLParserContext<'input> for OpBitXorAssignContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for OpBitXorAssignContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_OpBitXorAssign(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_OpBitXorAssign(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for OpBitXorAssignContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_assignOp }
	//fn type_rule_index() -> usize where Self: Sized { RULE_assignOp }
}

impl<'input> Borrow<AssignOpContextExt<'input>> for OpBitXorAssignContext<'input>{
	fn borrow(&self) -> &AssignOpContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<AssignOpContextExt<'input>> for OpBitXorAssignContext<'input>{
	fn borrow_mut(&mut self) -> &mut AssignOpContextExt<'input> { &mut self.__base }
}

impl<'input> AssignOpContextAttrs<'input> for OpBitXorAssignContext<'input> {}

impl<'input> OpBitXorAssignContextExt<'input>{
	fn new(ctx: &dyn AssignOpContextAttrs<'input>) -> Rc<AssignOpContextAll<'input>>  {
		Rc::new(
			AssignOpContextAll::OpBitXorAssignContext(
				BaseParserRuleContext::copy_from(ctx,OpBitXorAssignContextExt{
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type OpSubAssignContext<'input> = BaseParserRuleContext<'input,OpSubAssignContextExt<'input>>;

pub trait OpSubAssignContextAttrs<'input>: LibSLParserContext<'input>{
	/// Retrieves first TerminalNode corresponding to token MINUS_EQ
	/// Returns `None` if there is no child corresponding to token MINUS_EQ
	fn MINUS_EQ(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(MINUS_EQ, 0)
	}
}

impl<'input> OpSubAssignContextAttrs<'input> for OpSubAssignContext<'input>{}

pub struct OpSubAssignContextExt<'input>{
	__base:AssignOpContextExt<'input>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{OpSubAssignContextExt<'a>}

impl<'input> LibSLParserContext<'input> for OpSubAssignContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for OpSubAssignContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_OpSubAssign(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_OpSubAssign(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for OpSubAssignContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_assignOp }
	//fn type_rule_index() -> usize where Self: Sized { RULE_assignOp }
}

impl<'input> Borrow<AssignOpContextExt<'input>> for OpSubAssignContext<'input>{
	fn borrow(&self) -> &AssignOpContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<AssignOpContextExt<'input>> for OpSubAssignContext<'input>{
	fn borrow_mut(&mut self) -> &mut AssignOpContextExt<'input> { &mut self.__base }
}

impl<'input> AssignOpContextAttrs<'input> for OpSubAssignContext<'input> {}

impl<'input> OpSubAssignContextExt<'input>{
	fn new(ctx: &dyn AssignOpContextAttrs<'input>) -> Rc<AssignOpContextAll<'input>>  {
		Rc::new(
			AssignOpContextAll::OpSubAssignContext(
				BaseParserRuleContext::copy_from(ctx,OpSubAssignContextExt{
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type OpLShiftAssignContext<'input> = BaseParserRuleContext<'input,OpLShiftAssignContextExt<'input>>;

pub trait OpLShiftAssignContextAttrs<'input>: LibSLParserContext<'input>{
	/// Retrieves first TerminalNode corresponding to token L_ANGLE_L_ANGLE_EQ
	/// Returns `None` if there is no child corresponding to token L_ANGLE_L_ANGLE_EQ
	fn L_ANGLE_L_ANGLE_EQ(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(L_ANGLE_L_ANGLE_EQ, 0)
	}
}

impl<'input> OpLShiftAssignContextAttrs<'input> for OpLShiftAssignContext<'input>{}

pub struct OpLShiftAssignContextExt<'input>{
	__base:AssignOpContextExt<'input>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{OpLShiftAssignContextExt<'a>}

impl<'input> LibSLParserContext<'input> for OpLShiftAssignContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for OpLShiftAssignContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_OpLShiftAssign(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_OpLShiftAssign(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for OpLShiftAssignContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_assignOp }
	//fn type_rule_index() -> usize where Self: Sized { RULE_assignOp }
}

impl<'input> Borrow<AssignOpContextExt<'input>> for OpLShiftAssignContext<'input>{
	fn borrow(&self) -> &AssignOpContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<AssignOpContextExt<'input>> for OpLShiftAssignContext<'input>{
	fn borrow_mut(&mut self) -> &mut AssignOpContextExt<'input> { &mut self.__base }
}

impl<'input> AssignOpContextAttrs<'input> for OpLShiftAssignContext<'input> {}

impl<'input> OpLShiftAssignContextExt<'input>{
	fn new(ctx: &dyn AssignOpContextAttrs<'input>) -> Rc<AssignOpContextAll<'input>>  {
		Rc::new(
			AssignOpContextAll::OpLShiftAssignContext(
				BaseParserRuleContext::copy_from(ctx,OpLShiftAssignContextExt{
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type OpRShiftAssignContext<'input> = BaseParserRuleContext<'input,OpRShiftAssignContextExt<'input>>;

pub trait OpRShiftAssignContextAttrs<'input>: LibSLParserContext<'input>{
	/// Retrieves first TerminalNode corresponding to token R_ANGLE_R_ANGLE_EQ
	/// Returns `None` if there is no child corresponding to token R_ANGLE_R_ANGLE_EQ
	fn R_ANGLE_R_ANGLE_EQ(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(R_ANGLE_R_ANGLE_EQ, 0)
	}
}

impl<'input> OpRShiftAssignContextAttrs<'input> for OpRShiftAssignContext<'input>{}

pub struct OpRShiftAssignContextExt<'input>{
	__base:AssignOpContextExt<'input>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{OpRShiftAssignContextExt<'a>}

impl<'input> LibSLParserContext<'input> for OpRShiftAssignContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for OpRShiftAssignContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_OpRShiftAssign(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_OpRShiftAssign(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for OpRShiftAssignContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_assignOp }
	//fn type_rule_index() -> usize where Self: Sized { RULE_assignOp }
}

impl<'input> Borrow<AssignOpContextExt<'input>> for OpRShiftAssignContext<'input>{
	fn borrow(&self) -> &AssignOpContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<AssignOpContextExt<'input>> for OpRShiftAssignContext<'input>{
	fn borrow_mut(&mut self) -> &mut AssignOpContextExt<'input> { &mut self.__base }
}

impl<'input> AssignOpContextAttrs<'input> for OpRShiftAssignContext<'input> {}

impl<'input> OpRShiftAssignContextExt<'input>{
	fn new(ctx: &dyn AssignOpContextAttrs<'input>) -> Rc<AssignOpContextAll<'input>>  {
		Rc::new(
			AssignOpContextAll::OpRShiftAssignContext(
				BaseParserRuleContext::copy_from(ctx,OpRShiftAssignContextExt{
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type OpBitOrAssignContext<'input> = BaseParserRuleContext<'input,OpBitOrAssignContextExt<'input>>;

pub trait OpBitOrAssignContextAttrs<'input>: LibSLParserContext<'input>{
	/// Retrieves first TerminalNode corresponding to token PIPE_EQ
	/// Returns `None` if there is no child corresponding to token PIPE_EQ
	fn PIPE_EQ(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(PIPE_EQ, 0)
	}
}

impl<'input> OpBitOrAssignContextAttrs<'input> for OpBitOrAssignContext<'input>{}

pub struct OpBitOrAssignContextExt<'input>{
	__base:AssignOpContextExt<'input>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{OpBitOrAssignContextExt<'a>}

impl<'input> LibSLParserContext<'input> for OpBitOrAssignContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for OpBitOrAssignContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_OpBitOrAssign(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_OpBitOrAssign(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for OpBitOrAssignContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_assignOp }
	//fn type_rule_index() -> usize where Self: Sized { RULE_assignOp }
}

impl<'input> Borrow<AssignOpContextExt<'input>> for OpBitOrAssignContext<'input>{
	fn borrow(&self) -> &AssignOpContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<AssignOpContextExt<'input>> for OpBitOrAssignContext<'input>{
	fn borrow_mut(&mut self) -> &mut AssignOpContextExt<'input> { &mut self.__base }
}

impl<'input> AssignOpContextAttrs<'input> for OpBitOrAssignContext<'input> {}

impl<'input> OpBitOrAssignContextExt<'input>{
	fn new(ctx: &dyn AssignOpContextAttrs<'input>) -> Rc<AssignOpContextAll<'input>>  {
		Rc::new(
			AssignOpContextAll::OpBitOrAssignContext(
				BaseParserRuleContext::copy_from(ctx,OpBitOrAssignContextExt{
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type OpMulAssignContext<'input> = BaseParserRuleContext<'input,OpMulAssignContextExt<'input>>;

pub trait OpMulAssignContextAttrs<'input>: LibSLParserContext<'input>{
	/// Retrieves first TerminalNode corresponding to token ASTERISK_EQ
	/// Returns `None` if there is no child corresponding to token ASTERISK_EQ
	fn ASTERISK_EQ(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(ASTERISK_EQ, 0)
	}
}

impl<'input> OpMulAssignContextAttrs<'input> for OpMulAssignContext<'input>{}

pub struct OpMulAssignContextExt<'input>{
	__base:AssignOpContextExt<'input>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{OpMulAssignContextExt<'a>}

impl<'input> LibSLParserContext<'input> for OpMulAssignContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for OpMulAssignContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_OpMulAssign(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_OpMulAssign(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for OpMulAssignContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_assignOp }
	//fn type_rule_index() -> usize where Self: Sized { RULE_assignOp }
}

impl<'input> Borrow<AssignOpContextExt<'input>> for OpMulAssignContext<'input>{
	fn borrow(&self) -> &AssignOpContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<AssignOpContextExt<'input>> for OpMulAssignContext<'input>{
	fn borrow_mut(&mut self) -> &mut AssignOpContextExt<'input> { &mut self.__base }
}

impl<'input> AssignOpContextAttrs<'input> for OpMulAssignContext<'input> {}

impl<'input> OpMulAssignContextExt<'input>{
	fn new(ctx: &dyn AssignOpContextAttrs<'input>) -> Rc<AssignOpContextAll<'input>>  {
		Rc::new(
			AssignOpContextAll::OpMulAssignContext(
				BaseParserRuleContext::copy_from(ctx,OpMulAssignContextExt{
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type OpAssignContext<'input> = BaseParserRuleContext<'input,OpAssignContextExt<'input>>;

pub trait OpAssignContextAttrs<'input>: LibSLParserContext<'input>{
	/// Retrieves first TerminalNode corresponding to token EQ
	/// Returns `None` if there is no child corresponding to token EQ
	fn EQ(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(EQ, 0)
	}
}

impl<'input> OpAssignContextAttrs<'input> for OpAssignContext<'input>{}

pub struct OpAssignContextExt<'input>{
	__base:AssignOpContextExt<'input>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{OpAssignContextExt<'a>}

impl<'input> LibSLParserContext<'input> for OpAssignContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for OpAssignContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_OpAssign(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_OpAssign(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for OpAssignContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_assignOp }
	//fn type_rule_index() -> usize where Self: Sized { RULE_assignOp }
}

impl<'input> Borrow<AssignOpContextExt<'input>> for OpAssignContext<'input>{
	fn borrow(&self) -> &AssignOpContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<AssignOpContextExt<'input>> for OpAssignContext<'input>{
	fn borrow_mut(&mut self) -> &mut AssignOpContextExt<'input> { &mut self.__base }
}

impl<'input> AssignOpContextAttrs<'input> for OpAssignContext<'input> {}

impl<'input> OpAssignContextExt<'input>{
	fn new(ctx: &dyn AssignOpContextAttrs<'input>) -> Rc<AssignOpContextAll<'input>>  {
		Rc::new(
			AssignOpContextAll::OpAssignContext(
				BaseParserRuleContext::copy_from(ctx,OpAssignContextExt{
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type OpDivAssignContext<'input> = BaseParserRuleContext<'input,OpDivAssignContextExt<'input>>;

pub trait OpDivAssignContextAttrs<'input>: LibSLParserContext<'input>{
	/// Retrieves first TerminalNode corresponding to token SLASH_EQ
	/// Returns `None` if there is no child corresponding to token SLASH_EQ
	fn SLASH_EQ(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(SLASH_EQ, 0)
	}
}

impl<'input> OpDivAssignContextAttrs<'input> for OpDivAssignContext<'input>{}

pub struct OpDivAssignContextExt<'input>{
	__base:AssignOpContextExt<'input>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{OpDivAssignContextExt<'a>}

impl<'input> LibSLParserContext<'input> for OpDivAssignContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for OpDivAssignContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_OpDivAssign(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_OpDivAssign(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for OpDivAssignContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_assignOp }
	//fn type_rule_index() -> usize where Self: Sized { RULE_assignOp }
}

impl<'input> Borrow<AssignOpContextExt<'input>> for OpDivAssignContext<'input>{
	fn borrow(&self) -> &AssignOpContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<AssignOpContextExt<'input>> for OpDivAssignContext<'input>{
	fn borrow_mut(&mut self) -> &mut AssignOpContextExt<'input> { &mut self.__base }
}

impl<'input> AssignOpContextAttrs<'input> for OpDivAssignContext<'input> {}

impl<'input> OpDivAssignContextExt<'input>{
	fn new(ctx: &dyn AssignOpContextAttrs<'input>) -> Rc<AssignOpContextAll<'input>>  {
		Rc::new(
			AssignOpContextAll::OpDivAssignContext(
				BaseParserRuleContext::copy_from(ctx,OpDivAssignContextExt{
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

impl<'input, I, H> LibSLParser<'input, I, H>
where
    I: TokenStream<'input, TF = LocalTokenFactory<'input> > + TidAble<'input>,
    H: ErrorStrategy<'input,BaseParserType<'input,I>>
{
	pub fn assignOp(&mut self,)
	-> Result<Rc<AssignOpContextAll<'input>>,ANTLRError> {
		let mut recog = self;
		let _parentctx = recog.ctx.take();
		let mut _localctx = AssignOpContextExt::new(_parentctx.clone(), recog.base.get_state());
        recog.base.enter_rule(_localctx.clone(), 170, RULE_assignOp);
        let mut _localctx: Rc<AssignOpContextAll> = _localctx;
		let result: Result<(), ANTLRError> = (|| {

			recog.base.set_state(1112);
			recog.err_handler.sync(&mut recog.base)?;
			match recog.base.input.la(1) {
			 EQ 
				=> {
					let tmp = OpAssignContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 1);
					_localctx = tmp;
					{
					recog.base.set_state(1101);
					recog.base.match_token(EQ,&mut recog.err_handler)?;

					}
				}

			 PLUS_EQ 
				=> {
					let tmp = OpAddAssignContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 2);
					_localctx = tmp;
					{
					recog.base.set_state(1102);
					recog.base.match_token(PLUS_EQ,&mut recog.err_handler)?;

					}
				}

			 MINUS_EQ 
				=> {
					let tmp = OpSubAssignContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 3);
					_localctx = tmp;
					{
					recog.base.set_state(1103);
					recog.base.match_token(MINUS_EQ,&mut recog.err_handler)?;

					}
				}

			 ASTERISK_EQ 
				=> {
					let tmp = OpMulAssignContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 4);
					_localctx = tmp;
					{
					recog.base.set_state(1104);
					recog.base.match_token(ASTERISK_EQ,&mut recog.err_handler)?;

					}
				}

			 SLASH_EQ 
				=> {
					let tmp = OpDivAssignContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 5);
					_localctx = tmp;
					{
					recog.base.set_state(1105);
					recog.base.match_token(SLASH_EQ,&mut recog.err_handler)?;

					}
				}

			 PERCENT_EQ 
				=> {
					let tmp = OpModAssignContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 6);
					_localctx = tmp;
					{
					recog.base.set_state(1106);
					recog.base.match_token(PERCENT_EQ,&mut recog.err_handler)?;

					}
				}

			 AMP_EQ 
				=> {
					let tmp = OpBitAndAssignContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 7);
					_localctx = tmp;
					{
					recog.base.set_state(1107);
					recog.base.match_token(AMP_EQ,&mut recog.err_handler)?;

					}
				}

			 PIPE_EQ 
				=> {
					let tmp = OpBitOrAssignContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 8);
					_localctx = tmp;
					{
					recog.base.set_state(1108);
					recog.base.match_token(PIPE_EQ,&mut recog.err_handler)?;

					}
				}

			 CARET_EQ 
				=> {
					let tmp = OpBitXorAssignContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 9);
					_localctx = tmp;
					{
					recog.base.set_state(1109);
					recog.base.match_token(CARET_EQ,&mut recog.err_handler)?;

					}
				}

			 L_ANGLE_L_ANGLE_EQ 
				=> {
					let tmp = OpLShiftAssignContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 10);
					_localctx = tmp;
					{
					recog.base.set_state(1110);
					recog.base.match_token(L_ANGLE_L_ANGLE_EQ,&mut recog.err_handler)?;

					}
				}

			 R_ANGLE_R_ANGLE_EQ 
				=> {
					let tmp = OpRShiftAssignContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 11);
					_localctx = tmp;
					{
					recog.base.set_state(1111);
					recog.base.match_token(R_ANGLE_R_ANGLE_EQ,&mut recog.err_handler)?;

					}
				}

				_ => Err(ANTLRError::NoAltError(NoViableAltError::new(&mut recog.base)))?
			}
			Ok(())
		})();
		match result {
		Ok(_)=>{},
        Err(e @ ANTLRError::FallThrough(_)) => return Err(e),
		Err(ref re) => {
				//_localctx.exception = re;
				recog.err_handler.report_error(&mut recog.base, re);
				recog.err_handler.recover(&mut recog.base, re)?;
			}
		}
		recog.base.exit_rule();

		Ok(_localctx)
	}
}
//------------------- exprList ----------------
pub type ExprListContextAll<'input> = ExprListContext<'input>;


pub type ExprListContext<'input> = BaseParserRuleContext<'input,ExprListContextExt<'input>>;

#[derive(Clone)]
pub struct ExprListContextExt<'input>{
	pub expr: Option<Rc<ExprContextAll<'input>>>,
	pub exprs:Vec<Rc<ExprContextAll<'input>>>,
ph:PhantomData<&'input str>
}

impl<'input> LibSLParserContext<'input> for ExprListContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for ExprListContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_exprList(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_exprList(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for ExprListContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_exprList }
	//fn type_rule_index() -> usize where Self: Sized { RULE_exprList }
}
antlr_rust::tid!{ExprListContextExt<'a>}

impl<'input> ExprListContextExt<'input>{
	fn new(parent: Option<Rc<dyn LibSLParserContext<'input> + 'input > >, invoking_state: isize) -> Rc<ExprListContextAll<'input>> {
		Rc::new(
			BaseParserRuleContext::new_parser_ctx(parent, invoking_state,ExprListContextExt{
				expr: None, 
				exprs: Vec::new(), 
				ph:PhantomData
			}),
		)
	}
}

pub trait ExprListContextAttrs<'input>: LibSLParserContext<'input> + BorrowMut<ExprListContextExt<'input>>{

fn expr_all(&self) ->  Vec<Rc<ExprContextAll<'input>>> where Self:Sized{
	self.children_of_type()
}
fn expr(&self, i: usize) -> Option<Rc<ExprContextAll<'input>>> where Self:Sized{
	self.child_of_type(i)
}
/// Retrieves all `TerminalNode`s corresponding to token COMMA in current rule
fn COMMA_all(&self) -> Vec<Rc<TerminalNode<'input,LibSLParserContextType>>>  where Self:Sized{
	self.get_tokens(COMMA)
}
/// Retrieves 'i's TerminalNode corresponding to token COMMA, starting from 0.
/// Returns `None` if number of children corresponding to token COMMA is less or equal than `i`.
fn COMMA(&self, i: usize) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(COMMA, i)
}

}

impl<'input> ExprListContextAttrs<'input> for ExprListContext<'input>{}

impl<'input, I, H> LibSLParser<'input, I, H>
where
    I: TokenStream<'input, TF = LocalTokenFactory<'input> > + TidAble<'input>,
    H: ErrorStrategy<'input,BaseParserType<'input,I>>
{
	pub fn exprList(&mut self,)
	-> Result<Rc<ExprListContextAll<'input>>,ANTLRError> {
		let mut recog = self;
		let _parentctx = recog.ctx.take();
		let mut _localctx = ExprListContextExt::new(_parentctx.clone(), recog.base.get_state());
        recog.base.enter_rule(_localctx.clone(), 172, RULE_exprList);
        let mut _localctx: Rc<ExprListContextAll> = _localctx;
		let result: Result<(), ANTLRError> = (|| {

			let mut _alt: isize;
			//recog.base.enter_outer_alt(_localctx.clone(), 1);
			recog.base.enter_outer_alt(None, 1);
			{
			/*InvokeRule expr*/
			recog.base.set_state(1114);
			let tmp = recog.expr_rec(0)?;
			 cast_mut::<_,ExprListContext >(&mut _localctx).expr = Some(tmp.clone());
			  

			let temp =  cast_mut::<_,ExprListContext >(&mut _localctx).expr.clone().unwrap()
			 ;
			 cast_mut::<_,ExprListContext >(&mut _localctx).exprs.push(temp);
			  
			recog.base.set_state(1119);
			recog.err_handler.sync(&mut recog.base)?;
			_alt = recog.interpreter.adaptive_predict(146,&mut recog.base)?;
			while { _alt!=2 && _alt!=INVALID_ALT } {
				if _alt==1 {
					{
					{
					recog.base.set_state(1115);
					recog.base.match_token(COMMA,&mut recog.err_handler)?;

					/*InvokeRule expr*/
					recog.base.set_state(1116);
					let tmp = recog.expr_rec(0)?;
					 cast_mut::<_,ExprListContext >(&mut _localctx).expr = Some(tmp.clone());
					  

					let temp =  cast_mut::<_,ExprListContext >(&mut _localctx).expr.clone().unwrap()
					 ;
					 cast_mut::<_,ExprListContext >(&mut _localctx).exprs.push(temp);
					  
					}
					} 
				}
				recog.base.set_state(1121);
				recog.err_handler.sync(&mut recog.base)?;
				_alt = recog.interpreter.adaptive_predict(146,&mut recog.base)?;
			}
			}
			Ok(())
		})();
		match result {
		Ok(_)=>{},
        Err(e @ ANTLRError::FallThrough(_)) => return Err(e),
		Err(ref re) => {
				//_localctx.exception = re;
				recog.err_handler.report_error(&mut recog.base, re);
				recog.err_handler.recover(&mut recog.base, re)?;
			}
		}
		recog.base.exit_rule();

		Ok(_localctx)
	}
}
//------------------- atomicExpr ----------------
#[derive(Debug)]
pub enum AtomicExprContextAll<'input>{
	AtomicExprArrayLitContext(AtomicExprArrayLitContext<'input>),
	AtomicExprPrimitiveLitContext(AtomicExprPrimitiveLitContext<'input>),
	AtomicExprSignedNumLitContext(AtomicExprSignedNumLitContext<'input>),
	AtomicExprNameContext(AtomicExprNameContext<'input>),
	AtomicExprParenContext(AtomicExprParenContext<'input>),
	AtomicExprSetLitContext(AtomicExprSetLitContext<'input>),
Error(AtomicExprContext<'input>)
}
antlr_rust::tid!{AtomicExprContextAll<'a>}

impl<'input> antlr_rust::parser_rule_context::DerefSeal for AtomicExprContextAll<'input>{}

impl<'input> LibSLParserContext<'input> for AtomicExprContextAll<'input>{}

impl<'input> Deref for AtomicExprContextAll<'input>{
	type Target = dyn AtomicExprContextAttrs<'input> + 'input;
	fn deref(&self) -> &Self::Target{
		use AtomicExprContextAll::*;
		match self{
			AtomicExprArrayLitContext(inner) => inner,
			AtomicExprPrimitiveLitContext(inner) => inner,
			AtomicExprSignedNumLitContext(inner) => inner,
			AtomicExprNameContext(inner) => inner,
			AtomicExprParenContext(inner) => inner,
			AtomicExprSetLitContext(inner) => inner,
Error(inner) => inner
		}
	}
}
impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for AtomicExprContextAll<'input>{
    fn enter(&self, listener: &mut (dyn LibSLParserListener<'input> + 'a)) { self.deref().enter(listener) }
    fn exit(&self, listener: &mut (dyn LibSLParserListener<'input> + 'a)) { self.deref().exit(listener) }
}



pub type AtomicExprContext<'input> = BaseParserRuleContext<'input,AtomicExprContextExt<'input>>;

#[derive(Clone)]
pub struct AtomicExprContextExt<'input>{
ph:PhantomData<&'input str>
}

impl<'input> LibSLParserContext<'input> for AtomicExprContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for AtomicExprContext<'input>{
}

impl<'input> CustomRuleContext<'input> for AtomicExprContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_atomicExpr }
	//fn type_rule_index() -> usize where Self: Sized { RULE_atomicExpr }
}
antlr_rust::tid!{AtomicExprContextExt<'a>}

impl<'input> AtomicExprContextExt<'input>{
	fn new(parent: Option<Rc<dyn LibSLParserContext<'input> + 'input > >, invoking_state: isize) -> Rc<AtomicExprContextAll<'input>> {
		Rc::new(
		AtomicExprContextAll::Error(
			BaseParserRuleContext::new_parser_ctx(parent, invoking_state,AtomicExprContextExt{
				ph:PhantomData
			}),
		)
		)
	}
}

pub trait AtomicExprContextAttrs<'input>: LibSLParserContext<'input> + BorrowMut<AtomicExprContextExt<'input>>{


}

impl<'input> AtomicExprContextAttrs<'input> for AtomicExprContext<'input>{}

pub type AtomicExprArrayLitContext<'input> = BaseParserRuleContext<'input,AtomicExprArrayLitContextExt<'input>>;

pub trait AtomicExprArrayLitContextAttrs<'input>: LibSLParserContext<'input>{
	fn arrayLitExpr(&self) -> Option<Rc<ArrayLitExprContextAll<'input>>> where Self:Sized{
		self.child_of_type(0)
	}
}

impl<'input> AtomicExprArrayLitContextAttrs<'input> for AtomicExprArrayLitContext<'input>{}

pub struct AtomicExprArrayLitContextExt<'input>{
	__base:AtomicExprContextExt<'input>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{AtomicExprArrayLitContextExt<'a>}

impl<'input> LibSLParserContext<'input> for AtomicExprArrayLitContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for AtomicExprArrayLitContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_AtomicExprArrayLit(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_AtomicExprArrayLit(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for AtomicExprArrayLitContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_atomicExpr }
	//fn type_rule_index() -> usize where Self: Sized { RULE_atomicExpr }
}

impl<'input> Borrow<AtomicExprContextExt<'input>> for AtomicExprArrayLitContext<'input>{
	fn borrow(&self) -> &AtomicExprContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<AtomicExprContextExt<'input>> for AtomicExprArrayLitContext<'input>{
	fn borrow_mut(&mut self) -> &mut AtomicExprContextExt<'input> { &mut self.__base }
}

impl<'input> AtomicExprContextAttrs<'input> for AtomicExprArrayLitContext<'input> {}

impl<'input> AtomicExprArrayLitContextExt<'input>{
	fn new(ctx: &dyn AtomicExprContextAttrs<'input>) -> Rc<AtomicExprContextAll<'input>>  {
		Rc::new(
			AtomicExprContextAll::AtomicExprArrayLitContext(
				BaseParserRuleContext::copy_from(ctx,AtomicExprArrayLitContextExt{
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type AtomicExprPrimitiveLitContext<'input> = BaseParserRuleContext<'input,AtomicExprPrimitiveLitContextExt<'input>>;

pub trait AtomicExprPrimitiveLitContextAttrs<'input>: LibSLParserContext<'input>{
	fn primitiveLit(&self) -> Option<Rc<PrimitiveLitContextAll<'input>>> where Self:Sized{
		self.child_of_type(0)
	}
}

impl<'input> AtomicExprPrimitiveLitContextAttrs<'input> for AtomicExprPrimitiveLitContext<'input>{}

pub struct AtomicExprPrimitiveLitContextExt<'input>{
	__base:AtomicExprContextExt<'input>,
	pub lit: Option<Rc<PrimitiveLitContextAll<'input>>>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{AtomicExprPrimitiveLitContextExt<'a>}

impl<'input> LibSLParserContext<'input> for AtomicExprPrimitiveLitContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for AtomicExprPrimitiveLitContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_AtomicExprPrimitiveLit(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_AtomicExprPrimitiveLit(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for AtomicExprPrimitiveLitContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_atomicExpr }
	//fn type_rule_index() -> usize where Self: Sized { RULE_atomicExpr }
}

impl<'input> Borrow<AtomicExprContextExt<'input>> for AtomicExprPrimitiveLitContext<'input>{
	fn borrow(&self) -> &AtomicExprContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<AtomicExprContextExt<'input>> for AtomicExprPrimitiveLitContext<'input>{
	fn borrow_mut(&mut self) -> &mut AtomicExprContextExt<'input> { &mut self.__base }
}

impl<'input> AtomicExprContextAttrs<'input> for AtomicExprPrimitiveLitContext<'input> {}

impl<'input> AtomicExprPrimitiveLitContextExt<'input>{
	fn new(ctx: &dyn AtomicExprContextAttrs<'input>) -> Rc<AtomicExprContextAll<'input>>  {
		Rc::new(
			AtomicExprContextAll::AtomicExprPrimitiveLitContext(
				BaseParserRuleContext::copy_from(ctx,AtomicExprPrimitiveLitContextExt{
        			lit:None, 
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type AtomicExprSignedNumLitContext<'input> = BaseParserRuleContext<'input,AtomicExprSignedNumLitContextExt<'input>>;

pub trait AtomicExprSignedNumLitContextAttrs<'input>: LibSLParserContext<'input>{
	fn signedNumLit(&self) -> Option<Rc<SignedNumLitContextAll<'input>>> where Self:Sized{
		self.child_of_type(0)
	}
}

impl<'input> AtomicExprSignedNumLitContextAttrs<'input> for AtomicExprSignedNumLitContext<'input>{}

pub struct AtomicExprSignedNumLitContextExt<'input>{
	__base:AtomicExprContextExt<'input>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{AtomicExprSignedNumLitContextExt<'a>}

impl<'input> LibSLParserContext<'input> for AtomicExprSignedNumLitContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for AtomicExprSignedNumLitContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_AtomicExprSignedNumLit(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_AtomicExprSignedNumLit(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for AtomicExprSignedNumLitContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_atomicExpr }
	//fn type_rule_index() -> usize where Self: Sized { RULE_atomicExpr }
}

impl<'input> Borrow<AtomicExprContextExt<'input>> for AtomicExprSignedNumLitContext<'input>{
	fn borrow(&self) -> &AtomicExprContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<AtomicExprContextExt<'input>> for AtomicExprSignedNumLitContext<'input>{
	fn borrow_mut(&mut self) -> &mut AtomicExprContextExt<'input> { &mut self.__base }
}

impl<'input> AtomicExprContextAttrs<'input> for AtomicExprSignedNumLitContext<'input> {}

impl<'input> AtomicExprSignedNumLitContextExt<'input>{
	fn new(ctx: &dyn AtomicExprContextAttrs<'input>) -> Rc<AtomicExprContextAll<'input>>  {
		Rc::new(
			AtomicExprContextAll::AtomicExprSignedNumLitContext(
				BaseParserRuleContext::copy_from(ctx,AtomicExprSignedNumLitContextExt{
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type AtomicExprNameContext<'input> = BaseParserRuleContext<'input,AtomicExprNameContextExt<'input>>;

pub trait AtomicExprNameContextAttrs<'input>: LibSLParserContext<'input>{
	fn ident(&self) -> Option<Rc<IdentContextAll<'input>>> where Self:Sized{
		self.child_of_type(0)
	}
}

impl<'input> AtomicExprNameContextAttrs<'input> for AtomicExprNameContext<'input>{}

pub struct AtomicExprNameContextExt<'input>{
	__base:AtomicExprContextExt<'input>,
	pub name: Option<Rc<IdentContextAll<'input>>>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{AtomicExprNameContextExt<'a>}

impl<'input> LibSLParserContext<'input> for AtomicExprNameContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for AtomicExprNameContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_AtomicExprName(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_AtomicExprName(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for AtomicExprNameContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_atomicExpr }
	//fn type_rule_index() -> usize where Self: Sized { RULE_atomicExpr }
}

impl<'input> Borrow<AtomicExprContextExt<'input>> for AtomicExprNameContext<'input>{
	fn borrow(&self) -> &AtomicExprContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<AtomicExprContextExt<'input>> for AtomicExprNameContext<'input>{
	fn borrow_mut(&mut self) -> &mut AtomicExprContextExt<'input> { &mut self.__base }
}

impl<'input> AtomicExprContextAttrs<'input> for AtomicExprNameContext<'input> {}

impl<'input> AtomicExprNameContextExt<'input>{
	fn new(ctx: &dyn AtomicExprContextAttrs<'input>) -> Rc<AtomicExprContextAll<'input>>  {
		Rc::new(
			AtomicExprContextAll::AtomicExprNameContext(
				BaseParserRuleContext::copy_from(ctx,AtomicExprNameContextExt{
        			name:None, 
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type AtomicExprParenContext<'input> = BaseParserRuleContext<'input,AtomicExprParenContextExt<'input>>;

pub trait AtomicExprParenContextAttrs<'input>: LibSLParserContext<'input>{
	/// Retrieves first TerminalNode corresponding to token L_PAREN
	/// Returns `None` if there is no child corresponding to token L_PAREN
	fn L_PAREN(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(L_PAREN, 0)
	}
	/// Retrieves first TerminalNode corresponding to token R_PAREN
	/// Returns `None` if there is no child corresponding to token R_PAREN
	fn R_PAREN(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(R_PAREN, 0)
	}
	fn atomicExpr(&self) -> Option<Rc<AtomicExprContextAll<'input>>> where Self:Sized{
		self.child_of_type(0)
	}
}

impl<'input> AtomicExprParenContextAttrs<'input> for AtomicExprParenContext<'input>{}

pub struct AtomicExprParenContextExt<'input>{
	__base:AtomicExprContextExt<'input>,
	pub inner: Option<Rc<AtomicExprContextAll<'input>>>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{AtomicExprParenContextExt<'a>}

impl<'input> LibSLParserContext<'input> for AtomicExprParenContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for AtomicExprParenContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_AtomicExprParen(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_AtomicExprParen(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for AtomicExprParenContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_atomicExpr }
	//fn type_rule_index() -> usize where Self: Sized { RULE_atomicExpr }
}

impl<'input> Borrow<AtomicExprContextExt<'input>> for AtomicExprParenContext<'input>{
	fn borrow(&self) -> &AtomicExprContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<AtomicExprContextExt<'input>> for AtomicExprParenContext<'input>{
	fn borrow_mut(&mut self) -> &mut AtomicExprContextExt<'input> { &mut self.__base }
}

impl<'input> AtomicExprContextAttrs<'input> for AtomicExprParenContext<'input> {}

impl<'input> AtomicExprParenContextExt<'input>{
	fn new(ctx: &dyn AtomicExprContextAttrs<'input>) -> Rc<AtomicExprContextAll<'input>>  {
		Rc::new(
			AtomicExprContextAll::AtomicExprParenContext(
				BaseParserRuleContext::copy_from(ctx,AtomicExprParenContextExt{
        			inner:None, 
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type AtomicExprSetLitContext<'input> = BaseParserRuleContext<'input,AtomicExprSetLitContextExt<'input>>;

pub trait AtomicExprSetLitContextAttrs<'input>: LibSLParserContext<'input>{
	fn setLitExpr(&self) -> Option<Rc<SetLitExprContextAll<'input>>> where Self:Sized{
		self.child_of_type(0)
	}
}

impl<'input> AtomicExprSetLitContextAttrs<'input> for AtomicExprSetLitContext<'input>{}

pub struct AtomicExprSetLitContextExt<'input>{
	__base:AtomicExprContextExt<'input>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{AtomicExprSetLitContextExt<'a>}

impl<'input> LibSLParserContext<'input> for AtomicExprSetLitContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for AtomicExprSetLitContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_AtomicExprSetLit(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_AtomicExprSetLit(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for AtomicExprSetLitContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_atomicExpr }
	//fn type_rule_index() -> usize where Self: Sized { RULE_atomicExpr }
}

impl<'input> Borrow<AtomicExprContextExt<'input>> for AtomicExprSetLitContext<'input>{
	fn borrow(&self) -> &AtomicExprContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<AtomicExprContextExt<'input>> for AtomicExprSetLitContext<'input>{
	fn borrow_mut(&mut self) -> &mut AtomicExprContextExt<'input> { &mut self.__base }
}

impl<'input> AtomicExprContextAttrs<'input> for AtomicExprSetLitContext<'input> {}

impl<'input> AtomicExprSetLitContextExt<'input>{
	fn new(ctx: &dyn AtomicExprContextAttrs<'input>) -> Rc<AtomicExprContextAll<'input>>  {
		Rc::new(
			AtomicExprContextAll::AtomicExprSetLitContext(
				BaseParserRuleContext::copy_from(ctx,AtomicExprSetLitContextExt{
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

impl<'input, I, H> LibSLParser<'input, I, H>
where
    I: TokenStream<'input, TF = LocalTokenFactory<'input> > + TidAble<'input>,
    H: ErrorStrategy<'input,BaseParserType<'input,I>>
{
	pub fn atomicExpr(&mut self,)
	-> Result<Rc<AtomicExprContextAll<'input>>,ANTLRError> {
		let mut recog = self;
		let _parentctx = recog.ctx.take();
		let mut _localctx = AtomicExprContextExt::new(_parentctx.clone(), recog.base.get_state());
        recog.base.enter_rule(_localctx.clone(), 174, RULE_atomicExpr);
        let mut _localctx: Rc<AtomicExprContextAll> = _localctx;
		let result: Result<(), ANTLRError> = (|| {

			recog.base.set_state(1131);
			recog.err_handler.sync(&mut recog.base)?;
			match recog.base.input.la(1) {
			 L_PAREN 
				=> {
					let tmp = AtomicExprParenContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 1);
					_localctx = tmp;
					{
					recog.base.set_state(1122);
					recog.base.match_token(L_PAREN,&mut recog.err_handler)?;

					/*InvokeRule atomicExpr*/
					recog.base.set_state(1123);
					let tmp = recog.atomicExpr()?;
					if let AtomicExprContextAll::AtomicExprParenContext(ctx) = cast_mut::<_,AtomicExprContextAll >(&mut _localctx){
					ctx.inner = Some(tmp.clone()); } else {unreachable!("cant cast");}  

					recog.base.set_state(1124);
					recog.base.match_token(R_PAREN,&mut recog.err_handler)?;

					}
				}

			 TRUE | FALSE | NULL | IntegerLit | FloatLit | StringLit | CharacterLit 
				=> {
					let tmp = AtomicExprPrimitiveLitContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 2);
					_localctx = tmp;
					{
					/*InvokeRule primitiveLit*/
					recog.base.set_state(1126);
					let tmp = recog.primitiveLit()?;
					if let AtomicExprContextAll::AtomicExprPrimitiveLitContext(ctx) = cast_mut::<_,AtomicExprContextAll >(&mut _localctx){
					ctx.lit = Some(tmp.clone()); } else {unreachable!("cant cast");}  

					}
				}

			 PLUS | MINUS 
				=> {
					let tmp = AtomicExprSignedNumLitContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 3);
					_localctx = tmp;
					{
					/*InvokeRule signedNumLit*/
					recog.base.set_state(1127);
					recog.signedNumLit()?;

					}
				}

			 L_BRACKET 
				=> {
					let tmp = AtomicExprArrayLitContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 4);
					_localctx = tmp;
					{
					/*InvokeRule arrayLitExpr*/
					recog.base.set_state(1128);
					recog.arrayLitExpr()?;

					}
				}

			 L_BRACE 
				=> {
					let tmp = AtomicExprSetLitContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 5);
					_localctx = tmp;
					{
					/*InvokeRule setLitExpr*/
					recog.base.set_state(1129);
					recog.setLitExpr()?;

					}
				}

			 IMPLEMENTS | STATIC | PURE | Identifier 
				=> {
					let tmp = AtomicExprNameContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 6);
					_localctx = tmp;
					{
					/*InvokeRule ident*/
					recog.base.set_state(1130);
					let tmp = recog.ident()?;
					if let AtomicExprContextAll::AtomicExprNameContext(ctx) = cast_mut::<_,AtomicExprContextAll >(&mut _localctx){
					ctx.name = Some(tmp.clone()); } else {unreachable!("cant cast");}  

					}
				}

				_ => Err(ANTLRError::NoAltError(NoViableAltError::new(&mut recog.base)))?
			}
			Ok(())
		})();
		match result {
		Ok(_)=>{},
        Err(e @ ANTLRError::FallThrough(_)) => return Err(e),
		Err(ref re) => {
				//_localctx.exception = re;
				recog.err_handler.report_error(&mut recog.base, re);
				recog.err_handler.recover(&mut recog.base, re)?;
			}
		}
		recog.base.exit_rule();

		Ok(_localctx)
	}
}
//------------------- signedNumLit ----------------
#[derive(Debug)]
pub enum SignedNumLitContextAll<'input>{
	SignedNumLitFloatContext(SignedNumLitFloatContext<'input>),
	SignedNumLitIntContext(SignedNumLitIntContext<'input>),
Error(SignedNumLitContext<'input>)
}
antlr_rust::tid!{SignedNumLitContextAll<'a>}

impl<'input> antlr_rust::parser_rule_context::DerefSeal for SignedNumLitContextAll<'input>{}

impl<'input> LibSLParserContext<'input> for SignedNumLitContextAll<'input>{}

impl<'input> Deref for SignedNumLitContextAll<'input>{
	type Target = dyn SignedNumLitContextAttrs<'input> + 'input;
	fn deref(&self) -> &Self::Target{
		use SignedNumLitContextAll::*;
		match self{
			SignedNumLitFloatContext(inner) => inner,
			SignedNumLitIntContext(inner) => inner,
Error(inner) => inner
		}
	}
}
impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for SignedNumLitContextAll<'input>{
    fn enter(&self, listener: &mut (dyn LibSLParserListener<'input> + 'a)) { self.deref().enter(listener) }
    fn exit(&self, listener: &mut (dyn LibSLParserListener<'input> + 'a)) { self.deref().exit(listener) }
}



pub type SignedNumLitContext<'input> = BaseParserRuleContext<'input,SignedNumLitContextExt<'input>>;

#[derive(Clone)]
pub struct SignedNumLitContextExt<'input>{
ph:PhantomData<&'input str>
}

impl<'input> LibSLParserContext<'input> for SignedNumLitContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for SignedNumLitContext<'input>{
}

impl<'input> CustomRuleContext<'input> for SignedNumLitContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_signedNumLit }
	//fn type_rule_index() -> usize where Self: Sized { RULE_signedNumLit }
}
antlr_rust::tid!{SignedNumLitContextExt<'a>}

impl<'input> SignedNumLitContextExt<'input>{
	fn new(parent: Option<Rc<dyn LibSLParserContext<'input> + 'input > >, invoking_state: isize) -> Rc<SignedNumLitContextAll<'input>> {
		Rc::new(
		SignedNumLitContextAll::Error(
			BaseParserRuleContext::new_parser_ctx(parent, invoking_state,SignedNumLitContextExt{
				ph:PhantomData
			}),
		)
		)
	}
}

pub trait SignedNumLitContextAttrs<'input>: LibSLParserContext<'input> + BorrowMut<SignedNumLitContextExt<'input>>{


}

impl<'input> SignedNumLitContextAttrs<'input> for SignedNumLitContext<'input>{}

pub type SignedNumLitFloatContext<'input> = BaseParserRuleContext<'input,SignedNumLitFloatContextExt<'input>>;

pub trait SignedNumLitFloatContextAttrs<'input>: LibSLParserContext<'input>{
	fn sign(&self) -> Option<Rc<SignContextAll<'input>>> where Self:Sized{
		self.child_of_type(0)
	}
	/// Retrieves first TerminalNode corresponding to token FloatLit
	/// Returns `None` if there is no child corresponding to token FloatLit
	fn FloatLit(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(FloatLit, 0)
	}
}

impl<'input> SignedNumLitFloatContextAttrs<'input> for SignedNumLitFloatContext<'input>{}

pub struct SignedNumLitFloatContextExt<'input>{
	__base:SignedNumLitContextExt<'input>,
	pub lit: Option<TokenType<'input>>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{SignedNumLitFloatContextExt<'a>}

impl<'input> LibSLParserContext<'input> for SignedNumLitFloatContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for SignedNumLitFloatContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_SignedNumLitFloat(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_SignedNumLitFloat(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for SignedNumLitFloatContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_signedNumLit }
	//fn type_rule_index() -> usize where Self: Sized { RULE_signedNumLit }
}

impl<'input> Borrow<SignedNumLitContextExt<'input>> for SignedNumLitFloatContext<'input>{
	fn borrow(&self) -> &SignedNumLitContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<SignedNumLitContextExt<'input>> for SignedNumLitFloatContext<'input>{
	fn borrow_mut(&mut self) -> &mut SignedNumLitContextExt<'input> { &mut self.__base }
}

impl<'input> SignedNumLitContextAttrs<'input> for SignedNumLitFloatContext<'input> {}

impl<'input> SignedNumLitFloatContextExt<'input>{
	fn new(ctx: &dyn SignedNumLitContextAttrs<'input>) -> Rc<SignedNumLitContextAll<'input>>  {
		Rc::new(
			SignedNumLitContextAll::SignedNumLitFloatContext(
				BaseParserRuleContext::copy_from(ctx,SignedNumLitFloatContextExt{
					lit:None, 
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type SignedNumLitIntContext<'input> = BaseParserRuleContext<'input,SignedNumLitIntContextExt<'input>>;

pub trait SignedNumLitIntContextAttrs<'input>: LibSLParserContext<'input>{
	fn sign(&self) -> Option<Rc<SignContextAll<'input>>> where Self:Sized{
		self.child_of_type(0)
	}
	/// Retrieves first TerminalNode corresponding to token IntegerLit
	/// Returns `None` if there is no child corresponding to token IntegerLit
	fn IntegerLit(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(IntegerLit, 0)
	}
}

impl<'input> SignedNumLitIntContextAttrs<'input> for SignedNumLitIntContext<'input>{}

pub struct SignedNumLitIntContextExt<'input>{
	__base:SignedNumLitContextExt<'input>,
	pub lit: Option<TokenType<'input>>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{SignedNumLitIntContextExt<'a>}

impl<'input> LibSLParserContext<'input> for SignedNumLitIntContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for SignedNumLitIntContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_SignedNumLitInt(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_SignedNumLitInt(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for SignedNumLitIntContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_signedNumLit }
	//fn type_rule_index() -> usize where Self: Sized { RULE_signedNumLit }
}

impl<'input> Borrow<SignedNumLitContextExt<'input>> for SignedNumLitIntContext<'input>{
	fn borrow(&self) -> &SignedNumLitContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<SignedNumLitContextExt<'input>> for SignedNumLitIntContext<'input>{
	fn borrow_mut(&mut self) -> &mut SignedNumLitContextExt<'input> { &mut self.__base }
}

impl<'input> SignedNumLitContextAttrs<'input> for SignedNumLitIntContext<'input> {}

impl<'input> SignedNumLitIntContextExt<'input>{
	fn new(ctx: &dyn SignedNumLitContextAttrs<'input>) -> Rc<SignedNumLitContextAll<'input>>  {
		Rc::new(
			SignedNumLitContextAll::SignedNumLitIntContext(
				BaseParserRuleContext::copy_from(ctx,SignedNumLitIntContextExt{
					lit:None, 
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

impl<'input, I, H> LibSLParser<'input, I, H>
where
    I: TokenStream<'input, TF = LocalTokenFactory<'input> > + TidAble<'input>,
    H: ErrorStrategy<'input,BaseParserType<'input,I>>
{
	pub fn signedNumLit(&mut self,)
	-> Result<Rc<SignedNumLitContextAll<'input>>,ANTLRError> {
		let mut recog = self;
		let _parentctx = recog.ctx.take();
		let mut _localctx = SignedNumLitContextExt::new(_parentctx.clone(), recog.base.get_state());
        recog.base.enter_rule(_localctx.clone(), 176, RULE_signedNumLit);
        let mut _localctx: Rc<SignedNumLitContextAll> = _localctx;
		let result: Result<(), ANTLRError> = (|| {

			recog.base.set_state(1139);
			recog.err_handler.sync(&mut recog.base)?;
			match  recog.interpreter.adaptive_predict(148,&mut recog.base)? {
				1 =>{
					let tmp = SignedNumLitIntContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 1);
					_localctx = tmp;
					{
					/*InvokeRule sign*/
					recog.base.set_state(1133);
					recog.sign()?;

					recog.base.set_state(1134);
					let tmp = recog.base.match_token(IntegerLit,&mut recog.err_handler)?;
					if let SignedNumLitContextAll::SignedNumLitIntContext(ctx) = cast_mut::<_,SignedNumLitContextAll >(&mut _localctx){
					ctx.lit = Some(tmp.clone()); } else {unreachable!("cant cast");}  

					}
				}
			,
				2 =>{
					let tmp = SignedNumLitFloatContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 2);
					_localctx = tmp;
					{
					/*InvokeRule sign*/
					recog.base.set_state(1136);
					recog.sign()?;

					recog.base.set_state(1137);
					let tmp = recog.base.match_token(FloatLit,&mut recog.err_handler)?;
					if let SignedNumLitContextAll::SignedNumLitFloatContext(ctx) = cast_mut::<_,SignedNumLitContextAll >(&mut _localctx){
					ctx.lit = Some(tmp.clone()); } else {unreachable!("cant cast");}  

					}
				}

				_ => {}
			}
			Ok(())
		})();
		match result {
		Ok(_)=>{},
        Err(e @ ANTLRError::FallThrough(_)) => return Err(e),
		Err(ref re) => {
				//_localctx.exception = re;
				recog.err_handler.report_error(&mut recog.base, re);
				recog.err_handler.recover(&mut recog.base, re)?;
			}
		}
		recog.base.exit_rule();

		Ok(_localctx)
	}
}
//------------------- expr ----------------
#[derive(Debug)]
pub enum ExprContextAll<'input>{
	ExprProcCallUnqualifiedContext(ExprProcCallUnqualifiedContext<'input>),
	ExprPrevContext(ExprPrevContext<'input>),
	ExprActionCallContext(ExprActionCallContext<'input>),
	ExprBitXorContext(ExprBitXorContext<'input>),
	ExprIndexContext(ExprIndexContext<'input>),
	ExprHasConceptContext(ExprHasConceptContext<'input>),
	ExprTypeComparisonContext(ExprTypeComparisonContext<'input>),
	ExprArrayLitContext(ExprArrayLitContext<'input>),
	ExprOrContext(ExprOrContext<'input>),
	ExprCastContext(ExprCastContext<'input>),
	ExprPrimitiveLitContext(ExprPrimitiveLitContext<'input>),
	ExprMultiplicativeContext(ExprMultiplicativeContext<'input>),
	ExprSetLitContext(ExprSetLitContext<'input>),
	ExprParenContext(ExprParenContext<'input>),
	ExprInstantiationContext(ExprInstantiationContext<'input>),
	ExprNameContext(ExprNameContext<'input>),
	ExprFieldContext(ExprFieldContext<'input>),
	ExprRelationalContext(ExprRelationalContext<'input>),
	ExprShiftContext(ExprShiftContext<'input>),
	ExprAdditiveContext(ExprAdditiveContext<'input>),
	ExprBitOrContext(ExprBitOrContext<'input>),
	ExprAndContext(ExprAndContext<'input>),
	ExprDerefContext(ExprDerefContext<'input>),
	ExprUnaryContext(ExprUnaryContext<'input>),
	ExprProcCallQualifiedContext(ExprProcCallQualifiedContext<'input>),
	ExprBitAndContext(ExprBitAndContext<'input>),
Error(ExprContext<'input>)
}
antlr_rust::tid!{ExprContextAll<'a>}

impl<'input> antlr_rust::parser_rule_context::DerefSeal for ExprContextAll<'input>{}

impl<'input> LibSLParserContext<'input> for ExprContextAll<'input>{}

impl<'input> Deref for ExprContextAll<'input>{
	type Target = dyn ExprContextAttrs<'input> + 'input;
	fn deref(&self) -> &Self::Target{
		use ExprContextAll::*;
		match self{
			ExprProcCallUnqualifiedContext(inner) => inner,
			ExprPrevContext(inner) => inner,
			ExprActionCallContext(inner) => inner,
			ExprBitXorContext(inner) => inner,
			ExprIndexContext(inner) => inner,
			ExprHasConceptContext(inner) => inner,
			ExprTypeComparisonContext(inner) => inner,
			ExprArrayLitContext(inner) => inner,
			ExprOrContext(inner) => inner,
			ExprCastContext(inner) => inner,
			ExprPrimitiveLitContext(inner) => inner,
			ExprMultiplicativeContext(inner) => inner,
			ExprSetLitContext(inner) => inner,
			ExprParenContext(inner) => inner,
			ExprInstantiationContext(inner) => inner,
			ExprNameContext(inner) => inner,
			ExprFieldContext(inner) => inner,
			ExprRelationalContext(inner) => inner,
			ExprShiftContext(inner) => inner,
			ExprAdditiveContext(inner) => inner,
			ExprBitOrContext(inner) => inner,
			ExprAndContext(inner) => inner,
			ExprDerefContext(inner) => inner,
			ExprUnaryContext(inner) => inner,
			ExprProcCallQualifiedContext(inner) => inner,
			ExprBitAndContext(inner) => inner,
Error(inner) => inner
		}
	}
}
impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for ExprContextAll<'input>{
    fn enter(&self, listener: &mut (dyn LibSLParserListener<'input> + 'a)) { self.deref().enter(listener) }
    fn exit(&self, listener: &mut (dyn LibSLParserListener<'input> + 'a)) { self.deref().exit(listener) }
}



pub type ExprContext<'input> = BaseParserRuleContext<'input,ExprContextExt<'input>>;

#[derive(Clone)]
pub struct ExprContextExt<'input>{
ph:PhantomData<&'input str>
}

impl<'input> LibSLParserContext<'input> for ExprContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for ExprContext<'input>{
}

impl<'input> CustomRuleContext<'input> for ExprContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_expr }
	//fn type_rule_index() -> usize where Self: Sized { RULE_expr }
}
antlr_rust::tid!{ExprContextExt<'a>}

impl<'input> ExprContextExt<'input>{
	fn new(parent: Option<Rc<dyn LibSLParserContext<'input> + 'input > >, invoking_state: isize) -> Rc<ExprContextAll<'input>> {
		Rc::new(
		ExprContextAll::Error(
			BaseParserRuleContext::new_parser_ctx(parent, invoking_state,ExprContextExt{
				ph:PhantomData
			}),
		)
		)
	}
}

pub trait ExprContextAttrs<'input>: LibSLParserContext<'input> + BorrowMut<ExprContextExt<'input>>{


}

impl<'input> ExprContextAttrs<'input> for ExprContext<'input>{}

pub type ExprProcCallUnqualifiedContext<'input> = BaseParserRuleContext<'input,ExprProcCallUnqualifiedContextExt<'input>>;

pub trait ExprProcCallUnqualifiedContextAttrs<'input>: LibSLParserContext<'input>{
	/// Retrieves first TerminalNode corresponding to token L_PAREN
	/// Returns `None` if there is no child corresponding to token L_PAREN
	fn L_PAREN(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(L_PAREN, 0)
	}
	/// Retrieves first TerminalNode corresponding to token R_PAREN
	/// Returns `None` if there is no child corresponding to token R_PAREN
	fn R_PAREN(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(R_PAREN, 0)
	}
	fn ident(&self) -> Option<Rc<IdentContextAll<'input>>> where Self:Sized{
		self.child_of_type(0)
	}
	fn typeArgSpec(&self) -> Option<Rc<TypeArgSpecContextAll<'input>>> where Self:Sized{
		self.child_of_type(0)
	}
	fn exprList(&self) -> Option<Rc<ExprListContextAll<'input>>> where Self:Sized{
		self.child_of_type(0)
	}
	/// Retrieves first TerminalNode corresponding to token COMMA
	/// Returns `None` if there is no child corresponding to token COMMA
	fn COMMA(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(COMMA, 0)
	}
}

impl<'input> ExprProcCallUnqualifiedContextAttrs<'input> for ExprProcCallUnqualifiedContext<'input>{}

pub struct ExprProcCallUnqualifiedContextExt<'input>{
	__base:ExprContextExt<'input>,
	pub name: Option<Rc<IdentContextAll<'input>>>,
	pub typeArgs: Option<Rc<TypeArgSpecContextAll<'input>>>,
	pub args: Option<Rc<ExprListContextAll<'input>>>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{ExprProcCallUnqualifiedContextExt<'a>}

impl<'input> LibSLParserContext<'input> for ExprProcCallUnqualifiedContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for ExprProcCallUnqualifiedContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_ExprProcCallUnqualified(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_ExprProcCallUnqualified(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for ExprProcCallUnqualifiedContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_expr }
	//fn type_rule_index() -> usize where Self: Sized { RULE_expr }
}

impl<'input> Borrow<ExprContextExt<'input>> for ExprProcCallUnqualifiedContext<'input>{
	fn borrow(&self) -> &ExprContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<ExprContextExt<'input>> for ExprProcCallUnqualifiedContext<'input>{
	fn borrow_mut(&mut self) -> &mut ExprContextExt<'input> { &mut self.__base }
}

impl<'input> ExprContextAttrs<'input> for ExprProcCallUnqualifiedContext<'input> {}

impl<'input> ExprProcCallUnqualifiedContextExt<'input>{
	fn new(ctx: &dyn ExprContextAttrs<'input>) -> Rc<ExprContextAll<'input>>  {
		Rc::new(
			ExprContextAll::ExprProcCallUnqualifiedContext(
				BaseParserRuleContext::copy_from(ctx,ExprProcCallUnqualifiedContextExt{
        			name:None, typeArgs:None, args:None, 
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type ExprPrevContext<'input> = BaseParserRuleContext<'input,ExprPrevContextExt<'input>>;

pub trait ExprPrevContextAttrs<'input>: LibSLParserContext<'input>{
	/// Retrieves first TerminalNode corresponding to token QUOTE
	/// Returns `None` if there is no child corresponding to token QUOTE
	fn QUOTE(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(QUOTE, 0)
	}
	fn expr(&self) -> Option<Rc<ExprContextAll<'input>>> where Self:Sized{
		self.child_of_type(0)
	}
}

impl<'input> ExprPrevContextAttrs<'input> for ExprPrevContext<'input>{}

pub struct ExprPrevContextExt<'input>{
	__base:ExprContextExt<'input>,
	pub base: Option<Rc<ExprContextAll<'input>>>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{ExprPrevContextExt<'a>}

impl<'input> LibSLParserContext<'input> for ExprPrevContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for ExprPrevContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_ExprPrev(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_ExprPrev(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for ExprPrevContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_expr }
	//fn type_rule_index() -> usize where Self: Sized { RULE_expr }
}

impl<'input> Borrow<ExprContextExt<'input>> for ExprPrevContext<'input>{
	fn borrow(&self) -> &ExprContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<ExprContextExt<'input>> for ExprPrevContext<'input>{
	fn borrow_mut(&mut self) -> &mut ExprContextExt<'input> { &mut self.__base }
}

impl<'input> ExprContextAttrs<'input> for ExprPrevContext<'input> {}

impl<'input> ExprPrevContextExt<'input>{
	fn new(ctx: &dyn ExprContextAttrs<'input>) -> Rc<ExprContextAll<'input>>  {
		Rc::new(
			ExprContextAll::ExprPrevContext(
				BaseParserRuleContext::copy_from(ctx,ExprPrevContextExt{
        			base:None, 
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type ExprActionCallContext<'input> = BaseParserRuleContext<'input,ExprActionCallContextExt<'input>>;

pub trait ExprActionCallContextAttrs<'input>: LibSLParserContext<'input>{
	fn actionCallExpr(&self) -> Option<Rc<ActionCallExprContextAll<'input>>> where Self:Sized{
		self.child_of_type(0)
	}
}

impl<'input> ExprActionCallContextAttrs<'input> for ExprActionCallContext<'input>{}

pub struct ExprActionCallContextExt<'input>{
	__base:ExprContextExt<'input>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{ExprActionCallContextExt<'a>}

impl<'input> LibSLParserContext<'input> for ExprActionCallContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for ExprActionCallContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_ExprActionCall(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_ExprActionCall(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for ExprActionCallContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_expr }
	//fn type_rule_index() -> usize where Self: Sized { RULE_expr }
}

impl<'input> Borrow<ExprContextExt<'input>> for ExprActionCallContext<'input>{
	fn borrow(&self) -> &ExprContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<ExprContextExt<'input>> for ExprActionCallContext<'input>{
	fn borrow_mut(&mut self) -> &mut ExprContextExt<'input> { &mut self.__base }
}

impl<'input> ExprContextAttrs<'input> for ExprActionCallContext<'input> {}

impl<'input> ExprActionCallContextExt<'input>{
	fn new(ctx: &dyn ExprContextAttrs<'input>) -> Rc<ExprContextAll<'input>>  {
		Rc::new(
			ExprContextAll::ExprActionCallContext(
				BaseParserRuleContext::copy_from(ctx,ExprActionCallContextExt{
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type ExprBitXorContext<'input> = BaseParserRuleContext<'input,ExprBitXorContextExt<'input>>;

pub trait ExprBitXorContextAttrs<'input>: LibSLParserContext<'input>{
	/// Retrieves first TerminalNode corresponding to token CARET
	/// Returns `None` if there is no child corresponding to token CARET
	fn CARET(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(CARET, 0)
	}
	fn expr_all(&self) ->  Vec<Rc<ExprContextAll<'input>>> where Self:Sized{
		self.children_of_type()
	}
	fn expr(&self, i: usize) -> Option<Rc<ExprContextAll<'input>>> where Self:Sized{
		self.child_of_type(i)
	}
}

impl<'input> ExprBitXorContextAttrs<'input> for ExprBitXorContext<'input>{}

pub struct ExprBitXorContextExt<'input>{
	__base:ExprContextExt<'input>,
	pub lhs: Option<Rc<ExprContextAll<'input>>>,
	pub rhs: Option<Rc<ExprContextAll<'input>>>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{ExprBitXorContextExt<'a>}

impl<'input> LibSLParserContext<'input> for ExprBitXorContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for ExprBitXorContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_ExprBitXor(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_ExprBitXor(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for ExprBitXorContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_expr }
	//fn type_rule_index() -> usize where Self: Sized { RULE_expr }
}

impl<'input> Borrow<ExprContextExt<'input>> for ExprBitXorContext<'input>{
	fn borrow(&self) -> &ExprContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<ExprContextExt<'input>> for ExprBitXorContext<'input>{
	fn borrow_mut(&mut self) -> &mut ExprContextExt<'input> { &mut self.__base }
}

impl<'input> ExprContextAttrs<'input> for ExprBitXorContext<'input> {}

impl<'input> ExprBitXorContextExt<'input>{
	fn new(ctx: &dyn ExprContextAttrs<'input>) -> Rc<ExprContextAll<'input>>  {
		Rc::new(
			ExprContextAll::ExprBitXorContext(
				BaseParserRuleContext::copy_from(ctx,ExprBitXorContextExt{
        			lhs:None, rhs:None, 
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type ExprIndexContext<'input> = BaseParserRuleContext<'input,ExprIndexContextExt<'input>>;

pub trait ExprIndexContextAttrs<'input>: LibSLParserContext<'input>{
	/// Retrieves first TerminalNode corresponding to token L_BRACKET
	/// Returns `None` if there is no child corresponding to token L_BRACKET
	fn L_BRACKET(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(L_BRACKET, 0)
	}
	/// Retrieves first TerminalNode corresponding to token R_BRACKET
	/// Returns `None` if there is no child corresponding to token R_BRACKET
	fn R_BRACKET(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(R_BRACKET, 0)
	}
	fn expr_all(&self) ->  Vec<Rc<ExprContextAll<'input>>> where Self:Sized{
		self.children_of_type()
	}
	fn expr(&self, i: usize) -> Option<Rc<ExprContextAll<'input>>> where Self:Sized{
		self.child_of_type(i)
	}
}

impl<'input> ExprIndexContextAttrs<'input> for ExprIndexContext<'input>{}

pub struct ExprIndexContextExt<'input>{
	__base:ExprContextExt<'input>,
	pub base: Option<Rc<ExprContextAll<'input>>>,
	pub index: Option<Rc<ExprContextAll<'input>>>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{ExprIndexContextExt<'a>}

impl<'input> LibSLParserContext<'input> for ExprIndexContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for ExprIndexContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_ExprIndex(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_ExprIndex(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for ExprIndexContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_expr }
	//fn type_rule_index() -> usize where Self: Sized { RULE_expr }
}

impl<'input> Borrow<ExprContextExt<'input>> for ExprIndexContext<'input>{
	fn borrow(&self) -> &ExprContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<ExprContextExt<'input>> for ExprIndexContext<'input>{
	fn borrow_mut(&mut self) -> &mut ExprContextExt<'input> { &mut self.__base }
}

impl<'input> ExprContextAttrs<'input> for ExprIndexContext<'input> {}

impl<'input> ExprIndexContextExt<'input>{
	fn new(ctx: &dyn ExprContextAttrs<'input>) -> Rc<ExprContextAll<'input>>  {
		Rc::new(
			ExprContextAll::ExprIndexContext(
				BaseParserRuleContext::copy_from(ctx,ExprIndexContextExt{
        			base:None, index:None, 
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type ExprHasConceptContext<'input> = BaseParserRuleContext<'input,ExprHasConceptContextExt<'input>>;

pub trait ExprHasConceptContextAttrs<'input>: LibSLParserContext<'input>{
	/// Retrieves first TerminalNode corresponding to token HAS
	/// Returns `None` if there is no child corresponding to token HAS
	fn HAS(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(HAS, 0)
	}
	fn expr(&self) -> Option<Rc<ExprContextAll<'input>>> where Self:Sized{
		self.child_of_type(0)
	}
	fn ident(&self) -> Option<Rc<IdentContextAll<'input>>> where Self:Sized{
		self.child_of_type(0)
	}
	/// Retrieves first TerminalNode corresponding to token BANG
	/// Returns `None` if there is no child corresponding to token BANG
	fn BANG(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(BANG, 0)
	}
}

impl<'input> ExprHasConceptContextAttrs<'input> for ExprHasConceptContext<'input>{}

pub struct ExprHasConceptContextExt<'input>{
	__base:ExprContextExt<'input>,
	pub lhs: Option<Rc<ExprContextAll<'input>>>,
	pub not: Option<TokenType<'input>>,
	pub concept: Option<Rc<IdentContextAll<'input>>>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{ExprHasConceptContextExt<'a>}

impl<'input> LibSLParserContext<'input> for ExprHasConceptContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for ExprHasConceptContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_ExprHasConcept(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_ExprHasConcept(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for ExprHasConceptContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_expr }
	//fn type_rule_index() -> usize where Self: Sized { RULE_expr }
}

impl<'input> Borrow<ExprContextExt<'input>> for ExprHasConceptContext<'input>{
	fn borrow(&self) -> &ExprContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<ExprContextExt<'input>> for ExprHasConceptContext<'input>{
	fn borrow_mut(&mut self) -> &mut ExprContextExt<'input> { &mut self.__base }
}

impl<'input> ExprContextAttrs<'input> for ExprHasConceptContext<'input> {}

impl<'input> ExprHasConceptContextExt<'input>{
	fn new(ctx: &dyn ExprContextAttrs<'input>) -> Rc<ExprContextAll<'input>>  {
		Rc::new(
			ExprContextAll::ExprHasConceptContext(
				BaseParserRuleContext::copy_from(ctx,ExprHasConceptContextExt{
					not:None, 
        			lhs:None, concept:None, 
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type ExprTypeComparisonContext<'input> = BaseParserRuleContext<'input,ExprTypeComparisonContextExt<'input>>;

pub trait ExprTypeComparisonContextAttrs<'input>: LibSLParserContext<'input>{
	/// Retrieves first TerminalNode corresponding to token IS
	/// Returns `None` if there is no child corresponding to token IS
	fn IS(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(IS, 0)
	}
	fn expr(&self) -> Option<Rc<ExprContextAll<'input>>> where Self:Sized{
		self.child_of_type(0)
	}
	fn typeExpr(&self) -> Option<Rc<TypeExprContextAll<'input>>> where Self:Sized{
		self.child_of_type(0)
	}
	/// Retrieves first TerminalNode corresponding to token BANG
	/// Returns `None` if there is no child corresponding to token BANG
	fn BANG(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(BANG, 0)
	}
}

impl<'input> ExprTypeComparisonContextAttrs<'input> for ExprTypeComparisonContext<'input>{}

pub struct ExprTypeComparisonContextExt<'input>{
	__base:ExprContextExt<'input>,
	pub lhs: Option<Rc<ExprContextAll<'input>>>,
	pub not: Option<TokenType<'input>>,
	pub r#type: Option<Rc<TypeExprContextAll<'input>>>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{ExprTypeComparisonContextExt<'a>}

impl<'input> LibSLParserContext<'input> for ExprTypeComparisonContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for ExprTypeComparisonContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_ExprTypeComparison(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_ExprTypeComparison(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for ExprTypeComparisonContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_expr }
	//fn type_rule_index() -> usize where Self: Sized { RULE_expr }
}

impl<'input> Borrow<ExprContextExt<'input>> for ExprTypeComparisonContext<'input>{
	fn borrow(&self) -> &ExprContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<ExprContextExt<'input>> for ExprTypeComparisonContext<'input>{
	fn borrow_mut(&mut self) -> &mut ExprContextExt<'input> { &mut self.__base }
}

impl<'input> ExprContextAttrs<'input> for ExprTypeComparisonContext<'input> {}

impl<'input> ExprTypeComparisonContextExt<'input>{
	fn new(ctx: &dyn ExprContextAttrs<'input>) -> Rc<ExprContextAll<'input>>  {
		Rc::new(
			ExprContextAll::ExprTypeComparisonContext(
				BaseParserRuleContext::copy_from(ctx,ExprTypeComparisonContextExt{
					not:None, 
        			lhs:None, r#type:None, 
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type ExprArrayLitContext<'input> = BaseParserRuleContext<'input,ExprArrayLitContextExt<'input>>;

pub trait ExprArrayLitContextAttrs<'input>: LibSLParserContext<'input>{
	fn arrayLitExpr(&self) -> Option<Rc<ArrayLitExprContextAll<'input>>> where Self:Sized{
		self.child_of_type(0)
	}
}

impl<'input> ExprArrayLitContextAttrs<'input> for ExprArrayLitContext<'input>{}

pub struct ExprArrayLitContextExt<'input>{
	__base:ExprContextExt<'input>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{ExprArrayLitContextExt<'a>}

impl<'input> LibSLParserContext<'input> for ExprArrayLitContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for ExprArrayLitContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_ExprArrayLit(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_ExprArrayLit(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for ExprArrayLitContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_expr }
	//fn type_rule_index() -> usize where Self: Sized { RULE_expr }
}

impl<'input> Borrow<ExprContextExt<'input>> for ExprArrayLitContext<'input>{
	fn borrow(&self) -> &ExprContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<ExprContextExt<'input>> for ExprArrayLitContext<'input>{
	fn borrow_mut(&mut self) -> &mut ExprContextExt<'input> { &mut self.__base }
}

impl<'input> ExprContextAttrs<'input> for ExprArrayLitContext<'input> {}

impl<'input> ExprArrayLitContextExt<'input>{
	fn new(ctx: &dyn ExprContextAttrs<'input>) -> Rc<ExprContextAll<'input>>  {
		Rc::new(
			ExprContextAll::ExprArrayLitContext(
				BaseParserRuleContext::copy_from(ctx,ExprArrayLitContextExt{
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type ExprOrContext<'input> = BaseParserRuleContext<'input,ExprOrContextExt<'input>>;

pub trait ExprOrContextAttrs<'input>: LibSLParserContext<'input>{
	/// Retrieves first TerminalNode corresponding to token PIPE_PIPE
	/// Returns `None` if there is no child corresponding to token PIPE_PIPE
	fn PIPE_PIPE(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(PIPE_PIPE, 0)
	}
	fn expr_all(&self) ->  Vec<Rc<ExprContextAll<'input>>> where Self:Sized{
		self.children_of_type()
	}
	fn expr(&self, i: usize) -> Option<Rc<ExprContextAll<'input>>> where Self:Sized{
		self.child_of_type(i)
	}
}

impl<'input> ExprOrContextAttrs<'input> for ExprOrContext<'input>{}

pub struct ExprOrContextExt<'input>{
	__base:ExprContextExt<'input>,
	pub lhs: Option<Rc<ExprContextAll<'input>>>,
	pub rhs: Option<Rc<ExprContextAll<'input>>>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{ExprOrContextExt<'a>}

impl<'input> LibSLParserContext<'input> for ExprOrContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for ExprOrContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_ExprOr(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_ExprOr(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for ExprOrContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_expr }
	//fn type_rule_index() -> usize where Self: Sized { RULE_expr }
}

impl<'input> Borrow<ExprContextExt<'input>> for ExprOrContext<'input>{
	fn borrow(&self) -> &ExprContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<ExprContextExt<'input>> for ExprOrContext<'input>{
	fn borrow_mut(&mut self) -> &mut ExprContextExt<'input> { &mut self.__base }
}

impl<'input> ExprContextAttrs<'input> for ExprOrContext<'input> {}

impl<'input> ExprOrContextExt<'input>{
	fn new(ctx: &dyn ExprContextAttrs<'input>) -> Rc<ExprContextAll<'input>>  {
		Rc::new(
			ExprContextAll::ExprOrContext(
				BaseParserRuleContext::copy_from(ctx,ExprOrContextExt{
        			lhs:None, rhs:None, 
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type ExprCastContext<'input> = BaseParserRuleContext<'input,ExprCastContextExt<'input>>;

pub trait ExprCastContextAttrs<'input>: LibSLParserContext<'input>{
	/// Retrieves first TerminalNode corresponding to token AS
	/// Returns `None` if there is no child corresponding to token AS
	fn AS(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(AS, 0)
	}
	fn expr(&self) -> Option<Rc<ExprContextAll<'input>>> where Self:Sized{
		self.child_of_type(0)
	}
	fn typeExpr(&self) -> Option<Rc<TypeExprContextAll<'input>>> where Self:Sized{
		self.child_of_type(0)
	}
}

impl<'input> ExprCastContextAttrs<'input> for ExprCastContext<'input>{}

pub struct ExprCastContextExt<'input>{
	__base:ExprContextExt<'input>,
	pub lhs: Option<Rc<ExprContextAll<'input>>>,
	pub r#type: Option<Rc<TypeExprContextAll<'input>>>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{ExprCastContextExt<'a>}

impl<'input> LibSLParserContext<'input> for ExprCastContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for ExprCastContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_ExprCast(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_ExprCast(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for ExprCastContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_expr }
	//fn type_rule_index() -> usize where Self: Sized { RULE_expr }
}

impl<'input> Borrow<ExprContextExt<'input>> for ExprCastContext<'input>{
	fn borrow(&self) -> &ExprContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<ExprContextExt<'input>> for ExprCastContext<'input>{
	fn borrow_mut(&mut self) -> &mut ExprContextExt<'input> { &mut self.__base }
}

impl<'input> ExprContextAttrs<'input> for ExprCastContext<'input> {}

impl<'input> ExprCastContextExt<'input>{
	fn new(ctx: &dyn ExprContextAttrs<'input>) -> Rc<ExprContextAll<'input>>  {
		Rc::new(
			ExprContextAll::ExprCastContext(
				BaseParserRuleContext::copy_from(ctx,ExprCastContextExt{
        			lhs:None, r#type:None, 
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type ExprPrimitiveLitContext<'input> = BaseParserRuleContext<'input,ExprPrimitiveLitContextExt<'input>>;

pub trait ExprPrimitiveLitContextAttrs<'input>: LibSLParserContext<'input>{
	fn primitiveLit(&self) -> Option<Rc<PrimitiveLitContextAll<'input>>> where Self:Sized{
		self.child_of_type(0)
	}
}

impl<'input> ExprPrimitiveLitContextAttrs<'input> for ExprPrimitiveLitContext<'input>{}

pub struct ExprPrimitiveLitContextExt<'input>{
	__base:ExprContextExt<'input>,
	pub lit: Option<Rc<PrimitiveLitContextAll<'input>>>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{ExprPrimitiveLitContextExt<'a>}

impl<'input> LibSLParserContext<'input> for ExprPrimitiveLitContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for ExprPrimitiveLitContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_ExprPrimitiveLit(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_ExprPrimitiveLit(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for ExprPrimitiveLitContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_expr }
	//fn type_rule_index() -> usize where Self: Sized { RULE_expr }
}

impl<'input> Borrow<ExprContextExt<'input>> for ExprPrimitiveLitContext<'input>{
	fn borrow(&self) -> &ExprContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<ExprContextExt<'input>> for ExprPrimitiveLitContext<'input>{
	fn borrow_mut(&mut self) -> &mut ExprContextExt<'input> { &mut self.__base }
}

impl<'input> ExprContextAttrs<'input> for ExprPrimitiveLitContext<'input> {}

impl<'input> ExprPrimitiveLitContextExt<'input>{
	fn new(ctx: &dyn ExprContextAttrs<'input>) -> Rc<ExprContextAll<'input>>  {
		Rc::new(
			ExprContextAll::ExprPrimitiveLitContext(
				BaseParserRuleContext::copy_from(ctx,ExprPrimitiveLitContextExt{
        			lit:None, 
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type ExprMultiplicativeContext<'input> = BaseParserRuleContext<'input,ExprMultiplicativeContextExt<'input>>;

pub trait ExprMultiplicativeContextAttrs<'input>: LibSLParserContext<'input>{
	fn expr_all(&self) ->  Vec<Rc<ExprContextAll<'input>>> where Self:Sized{
		self.children_of_type()
	}
	fn expr(&self, i: usize) -> Option<Rc<ExprContextAll<'input>>> where Self:Sized{
		self.child_of_type(i)
	}
	fn mulBinOp(&self) -> Option<Rc<MulBinOpContextAll<'input>>> where Self:Sized{
		self.child_of_type(0)
	}
}

impl<'input> ExprMultiplicativeContextAttrs<'input> for ExprMultiplicativeContext<'input>{}

pub struct ExprMultiplicativeContextExt<'input>{
	__base:ExprContextExt<'input>,
	pub lhs: Option<Rc<ExprContextAll<'input>>>,
	pub op: Option<Rc<MulBinOpContextAll<'input>>>,
	pub rhs: Option<Rc<ExprContextAll<'input>>>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{ExprMultiplicativeContextExt<'a>}

impl<'input> LibSLParserContext<'input> for ExprMultiplicativeContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for ExprMultiplicativeContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_ExprMultiplicative(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_ExprMultiplicative(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for ExprMultiplicativeContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_expr }
	//fn type_rule_index() -> usize where Self: Sized { RULE_expr }
}

impl<'input> Borrow<ExprContextExt<'input>> for ExprMultiplicativeContext<'input>{
	fn borrow(&self) -> &ExprContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<ExprContextExt<'input>> for ExprMultiplicativeContext<'input>{
	fn borrow_mut(&mut self) -> &mut ExprContextExt<'input> { &mut self.__base }
}

impl<'input> ExprContextAttrs<'input> for ExprMultiplicativeContext<'input> {}

impl<'input> ExprMultiplicativeContextExt<'input>{
	fn new(ctx: &dyn ExprContextAttrs<'input>) -> Rc<ExprContextAll<'input>>  {
		Rc::new(
			ExprContextAll::ExprMultiplicativeContext(
				BaseParserRuleContext::copy_from(ctx,ExprMultiplicativeContextExt{
        			lhs:None, op:None, rhs:None, 
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type ExprSetLitContext<'input> = BaseParserRuleContext<'input,ExprSetLitContextExt<'input>>;

pub trait ExprSetLitContextAttrs<'input>: LibSLParserContext<'input>{
	fn setLitExpr(&self) -> Option<Rc<SetLitExprContextAll<'input>>> where Self:Sized{
		self.child_of_type(0)
	}
}

impl<'input> ExprSetLitContextAttrs<'input> for ExprSetLitContext<'input>{}

pub struct ExprSetLitContextExt<'input>{
	__base:ExprContextExt<'input>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{ExprSetLitContextExt<'a>}

impl<'input> LibSLParserContext<'input> for ExprSetLitContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for ExprSetLitContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_ExprSetLit(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_ExprSetLit(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for ExprSetLitContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_expr }
	//fn type_rule_index() -> usize where Self: Sized { RULE_expr }
}

impl<'input> Borrow<ExprContextExt<'input>> for ExprSetLitContext<'input>{
	fn borrow(&self) -> &ExprContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<ExprContextExt<'input>> for ExprSetLitContext<'input>{
	fn borrow_mut(&mut self) -> &mut ExprContextExt<'input> { &mut self.__base }
}

impl<'input> ExprContextAttrs<'input> for ExprSetLitContext<'input> {}

impl<'input> ExprSetLitContextExt<'input>{
	fn new(ctx: &dyn ExprContextAttrs<'input>) -> Rc<ExprContextAll<'input>>  {
		Rc::new(
			ExprContextAll::ExprSetLitContext(
				BaseParserRuleContext::copy_from(ctx,ExprSetLitContextExt{
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type ExprParenContext<'input> = BaseParserRuleContext<'input,ExprParenContextExt<'input>>;

pub trait ExprParenContextAttrs<'input>: LibSLParserContext<'input>{
	/// Retrieves first TerminalNode corresponding to token L_PAREN
	/// Returns `None` if there is no child corresponding to token L_PAREN
	fn L_PAREN(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(L_PAREN, 0)
	}
	/// Retrieves first TerminalNode corresponding to token R_PAREN
	/// Returns `None` if there is no child corresponding to token R_PAREN
	fn R_PAREN(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(R_PAREN, 0)
	}
	fn expr(&self) -> Option<Rc<ExprContextAll<'input>>> where Self:Sized{
		self.child_of_type(0)
	}
}

impl<'input> ExprParenContextAttrs<'input> for ExprParenContext<'input>{}

pub struct ExprParenContextExt<'input>{
	__base:ExprContextExt<'input>,
	pub inner: Option<Rc<ExprContextAll<'input>>>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{ExprParenContextExt<'a>}

impl<'input> LibSLParserContext<'input> for ExprParenContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for ExprParenContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_ExprParen(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_ExprParen(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for ExprParenContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_expr }
	//fn type_rule_index() -> usize where Self: Sized { RULE_expr }
}

impl<'input> Borrow<ExprContextExt<'input>> for ExprParenContext<'input>{
	fn borrow(&self) -> &ExprContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<ExprContextExt<'input>> for ExprParenContext<'input>{
	fn borrow_mut(&mut self) -> &mut ExprContextExt<'input> { &mut self.__base }
}

impl<'input> ExprContextAttrs<'input> for ExprParenContext<'input> {}

impl<'input> ExprParenContextExt<'input>{
	fn new(ctx: &dyn ExprContextAttrs<'input>) -> Rc<ExprContextAll<'input>>  {
		Rc::new(
			ExprContextAll::ExprParenContext(
				BaseParserRuleContext::copy_from(ctx,ExprParenContextExt{
        			inner:None, 
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type ExprInstantiationContext<'input> = BaseParserRuleContext<'input,ExprInstantiationContextExt<'input>>;

pub trait ExprInstantiationContextAttrs<'input>: LibSLParserContext<'input>{
	fn instantiationExpr(&self) -> Option<Rc<InstantiationExprContextAll<'input>>> where Self:Sized{
		self.child_of_type(0)
	}
}

impl<'input> ExprInstantiationContextAttrs<'input> for ExprInstantiationContext<'input>{}

pub struct ExprInstantiationContextExt<'input>{
	__base:ExprContextExt<'input>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{ExprInstantiationContextExt<'a>}

impl<'input> LibSLParserContext<'input> for ExprInstantiationContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for ExprInstantiationContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_ExprInstantiation(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_ExprInstantiation(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for ExprInstantiationContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_expr }
	//fn type_rule_index() -> usize where Self: Sized { RULE_expr }
}

impl<'input> Borrow<ExprContextExt<'input>> for ExprInstantiationContext<'input>{
	fn borrow(&self) -> &ExprContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<ExprContextExt<'input>> for ExprInstantiationContext<'input>{
	fn borrow_mut(&mut self) -> &mut ExprContextExt<'input> { &mut self.__base }
}

impl<'input> ExprContextAttrs<'input> for ExprInstantiationContext<'input> {}

impl<'input> ExprInstantiationContextExt<'input>{
	fn new(ctx: &dyn ExprContextAttrs<'input>) -> Rc<ExprContextAll<'input>>  {
		Rc::new(
			ExprContextAll::ExprInstantiationContext(
				BaseParserRuleContext::copy_from(ctx,ExprInstantiationContextExt{
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type ExprNameContext<'input> = BaseParserRuleContext<'input,ExprNameContextExt<'input>>;

pub trait ExprNameContextAttrs<'input>: LibSLParserContext<'input>{
	fn ident(&self) -> Option<Rc<IdentContextAll<'input>>> where Self:Sized{
		self.child_of_type(0)
	}
}

impl<'input> ExprNameContextAttrs<'input> for ExprNameContext<'input>{}

pub struct ExprNameContextExt<'input>{
	__base:ExprContextExt<'input>,
	pub name: Option<Rc<IdentContextAll<'input>>>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{ExprNameContextExt<'a>}

impl<'input> LibSLParserContext<'input> for ExprNameContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for ExprNameContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_ExprName(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_ExprName(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for ExprNameContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_expr }
	//fn type_rule_index() -> usize where Self: Sized { RULE_expr }
}

impl<'input> Borrow<ExprContextExt<'input>> for ExprNameContext<'input>{
	fn borrow(&self) -> &ExprContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<ExprContextExt<'input>> for ExprNameContext<'input>{
	fn borrow_mut(&mut self) -> &mut ExprContextExt<'input> { &mut self.__base }
}

impl<'input> ExprContextAttrs<'input> for ExprNameContext<'input> {}

impl<'input> ExprNameContextExt<'input>{
	fn new(ctx: &dyn ExprContextAttrs<'input>) -> Rc<ExprContextAll<'input>>  {
		Rc::new(
			ExprContextAll::ExprNameContext(
				BaseParserRuleContext::copy_from(ctx,ExprNameContextExt{
        			name:None, 
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type ExprFieldContext<'input> = BaseParserRuleContext<'input,ExprFieldContextExt<'input>>;

pub trait ExprFieldContextAttrs<'input>: LibSLParserContext<'input>{
	/// Retrieves first TerminalNode corresponding to token DOT
	/// Returns `None` if there is no child corresponding to token DOT
	fn DOT(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(DOT, 0)
	}
	fn expr(&self) -> Option<Rc<ExprContextAll<'input>>> where Self:Sized{
		self.child_of_type(0)
	}
	fn ident(&self) -> Option<Rc<IdentContextAll<'input>>> where Self:Sized{
		self.child_of_type(0)
	}
}

impl<'input> ExprFieldContextAttrs<'input> for ExprFieldContext<'input>{}

pub struct ExprFieldContextExt<'input>{
	__base:ExprContextExt<'input>,
	pub base: Option<Rc<ExprContextAll<'input>>>,
	pub field: Option<Rc<IdentContextAll<'input>>>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{ExprFieldContextExt<'a>}

impl<'input> LibSLParserContext<'input> for ExprFieldContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for ExprFieldContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_ExprField(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_ExprField(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for ExprFieldContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_expr }
	//fn type_rule_index() -> usize where Self: Sized { RULE_expr }
}

impl<'input> Borrow<ExprContextExt<'input>> for ExprFieldContext<'input>{
	fn borrow(&self) -> &ExprContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<ExprContextExt<'input>> for ExprFieldContext<'input>{
	fn borrow_mut(&mut self) -> &mut ExprContextExt<'input> { &mut self.__base }
}

impl<'input> ExprContextAttrs<'input> for ExprFieldContext<'input> {}

impl<'input> ExprFieldContextExt<'input>{
	fn new(ctx: &dyn ExprContextAttrs<'input>) -> Rc<ExprContextAll<'input>>  {
		Rc::new(
			ExprContextAll::ExprFieldContext(
				BaseParserRuleContext::copy_from(ctx,ExprFieldContextExt{
        			base:None, field:None, 
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type ExprRelationalContext<'input> = BaseParserRuleContext<'input,ExprRelationalContextExt<'input>>;

pub trait ExprRelationalContextAttrs<'input>: LibSLParserContext<'input>{
	fn expr_all(&self) ->  Vec<Rc<ExprContextAll<'input>>> where Self:Sized{
		self.children_of_type()
	}
	fn expr(&self, i: usize) -> Option<Rc<ExprContextAll<'input>>> where Self:Sized{
		self.child_of_type(i)
	}
	fn relOp(&self) -> Option<Rc<RelOpContextAll<'input>>> where Self:Sized{
		self.child_of_type(0)
	}
}

impl<'input> ExprRelationalContextAttrs<'input> for ExprRelationalContext<'input>{}

pub struct ExprRelationalContextExt<'input>{
	__base:ExprContextExt<'input>,
	pub lhs: Option<Rc<ExprContextAll<'input>>>,
	pub op: Option<Rc<RelOpContextAll<'input>>>,
	pub rhs: Option<Rc<ExprContextAll<'input>>>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{ExprRelationalContextExt<'a>}

impl<'input> LibSLParserContext<'input> for ExprRelationalContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for ExprRelationalContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_ExprRelational(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_ExprRelational(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for ExprRelationalContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_expr }
	//fn type_rule_index() -> usize where Self: Sized { RULE_expr }
}

impl<'input> Borrow<ExprContextExt<'input>> for ExprRelationalContext<'input>{
	fn borrow(&self) -> &ExprContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<ExprContextExt<'input>> for ExprRelationalContext<'input>{
	fn borrow_mut(&mut self) -> &mut ExprContextExt<'input> { &mut self.__base }
}

impl<'input> ExprContextAttrs<'input> for ExprRelationalContext<'input> {}

impl<'input> ExprRelationalContextExt<'input>{
	fn new(ctx: &dyn ExprContextAttrs<'input>) -> Rc<ExprContextAll<'input>>  {
		Rc::new(
			ExprContextAll::ExprRelationalContext(
				BaseParserRuleContext::copy_from(ctx,ExprRelationalContextExt{
        			lhs:None, op:None, rhs:None, 
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type ExprShiftContext<'input> = BaseParserRuleContext<'input,ExprShiftContextExt<'input>>;

pub trait ExprShiftContextAttrs<'input>: LibSLParserContext<'input>{
	fn expr_all(&self) ->  Vec<Rc<ExprContextAll<'input>>> where Self:Sized{
		self.children_of_type()
	}
	fn expr(&self, i: usize) -> Option<Rc<ExprContextAll<'input>>> where Self:Sized{
		self.child_of_type(i)
	}
	fn bitShiftOp(&self) -> Option<Rc<BitShiftOpContextAll<'input>>> where Self:Sized{
		self.child_of_type(0)
	}
}

impl<'input> ExprShiftContextAttrs<'input> for ExprShiftContext<'input>{}

pub struct ExprShiftContextExt<'input>{
	__base:ExprContextExt<'input>,
	pub lhs: Option<Rc<ExprContextAll<'input>>>,
	pub op: Option<Rc<BitShiftOpContextAll<'input>>>,
	pub rhs: Option<Rc<ExprContextAll<'input>>>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{ExprShiftContextExt<'a>}

impl<'input> LibSLParserContext<'input> for ExprShiftContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for ExprShiftContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_ExprShift(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_ExprShift(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for ExprShiftContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_expr }
	//fn type_rule_index() -> usize where Self: Sized { RULE_expr }
}

impl<'input> Borrow<ExprContextExt<'input>> for ExprShiftContext<'input>{
	fn borrow(&self) -> &ExprContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<ExprContextExt<'input>> for ExprShiftContext<'input>{
	fn borrow_mut(&mut self) -> &mut ExprContextExt<'input> { &mut self.__base }
}

impl<'input> ExprContextAttrs<'input> for ExprShiftContext<'input> {}

impl<'input> ExprShiftContextExt<'input>{
	fn new(ctx: &dyn ExprContextAttrs<'input>) -> Rc<ExprContextAll<'input>>  {
		Rc::new(
			ExprContextAll::ExprShiftContext(
				BaseParserRuleContext::copy_from(ctx,ExprShiftContextExt{
        			lhs:None, op:None, rhs:None, 
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type ExprAdditiveContext<'input> = BaseParserRuleContext<'input,ExprAdditiveContextExt<'input>>;

pub trait ExprAdditiveContextAttrs<'input>: LibSLParserContext<'input>{
	fn expr_all(&self) ->  Vec<Rc<ExprContextAll<'input>>> where Self:Sized{
		self.children_of_type()
	}
	fn expr(&self, i: usize) -> Option<Rc<ExprContextAll<'input>>> where Self:Sized{
		self.child_of_type(i)
	}
	fn addBinOp(&self) -> Option<Rc<AddBinOpContextAll<'input>>> where Self:Sized{
		self.child_of_type(0)
	}
}

impl<'input> ExprAdditiveContextAttrs<'input> for ExprAdditiveContext<'input>{}

pub struct ExprAdditiveContextExt<'input>{
	__base:ExprContextExt<'input>,
	pub lhs: Option<Rc<ExprContextAll<'input>>>,
	pub op: Option<Rc<AddBinOpContextAll<'input>>>,
	pub rhs: Option<Rc<ExprContextAll<'input>>>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{ExprAdditiveContextExt<'a>}

impl<'input> LibSLParserContext<'input> for ExprAdditiveContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for ExprAdditiveContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_ExprAdditive(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_ExprAdditive(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for ExprAdditiveContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_expr }
	//fn type_rule_index() -> usize where Self: Sized { RULE_expr }
}

impl<'input> Borrow<ExprContextExt<'input>> for ExprAdditiveContext<'input>{
	fn borrow(&self) -> &ExprContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<ExprContextExt<'input>> for ExprAdditiveContext<'input>{
	fn borrow_mut(&mut self) -> &mut ExprContextExt<'input> { &mut self.__base }
}

impl<'input> ExprContextAttrs<'input> for ExprAdditiveContext<'input> {}

impl<'input> ExprAdditiveContextExt<'input>{
	fn new(ctx: &dyn ExprContextAttrs<'input>) -> Rc<ExprContextAll<'input>>  {
		Rc::new(
			ExprContextAll::ExprAdditiveContext(
				BaseParserRuleContext::copy_from(ctx,ExprAdditiveContextExt{
        			lhs:None, op:None, rhs:None, 
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type ExprBitOrContext<'input> = BaseParserRuleContext<'input,ExprBitOrContextExt<'input>>;

pub trait ExprBitOrContextAttrs<'input>: LibSLParserContext<'input>{
	/// Retrieves first TerminalNode corresponding to token PIPE
	/// Returns `None` if there is no child corresponding to token PIPE
	fn PIPE(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(PIPE, 0)
	}
	fn expr_all(&self) ->  Vec<Rc<ExprContextAll<'input>>> where Self:Sized{
		self.children_of_type()
	}
	fn expr(&self, i: usize) -> Option<Rc<ExprContextAll<'input>>> where Self:Sized{
		self.child_of_type(i)
	}
}

impl<'input> ExprBitOrContextAttrs<'input> for ExprBitOrContext<'input>{}

pub struct ExprBitOrContextExt<'input>{
	__base:ExprContextExt<'input>,
	pub lhs: Option<Rc<ExprContextAll<'input>>>,
	pub rhs: Option<Rc<ExprContextAll<'input>>>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{ExprBitOrContextExt<'a>}

impl<'input> LibSLParserContext<'input> for ExprBitOrContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for ExprBitOrContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_ExprBitOr(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_ExprBitOr(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for ExprBitOrContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_expr }
	//fn type_rule_index() -> usize where Self: Sized { RULE_expr }
}

impl<'input> Borrow<ExprContextExt<'input>> for ExprBitOrContext<'input>{
	fn borrow(&self) -> &ExprContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<ExprContextExt<'input>> for ExprBitOrContext<'input>{
	fn borrow_mut(&mut self) -> &mut ExprContextExt<'input> { &mut self.__base }
}

impl<'input> ExprContextAttrs<'input> for ExprBitOrContext<'input> {}

impl<'input> ExprBitOrContextExt<'input>{
	fn new(ctx: &dyn ExprContextAttrs<'input>) -> Rc<ExprContextAll<'input>>  {
		Rc::new(
			ExprContextAll::ExprBitOrContext(
				BaseParserRuleContext::copy_from(ctx,ExprBitOrContextExt{
        			lhs:None, rhs:None, 
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type ExprAndContext<'input> = BaseParserRuleContext<'input,ExprAndContextExt<'input>>;

pub trait ExprAndContextAttrs<'input>: LibSLParserContext<'input>{
	/// Retrieves first TerminalNode corresponding to token AMP_AMP
	/// Returns `None` if there is no child corresponding to token AMP_AMP
	fn AMP_AMP(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(AMP_AMP, 0)
	}
	fn expr_all(&self) ->  Vec<Rc<ExprContextAll<'input>>> where Self:Sized{
		self.children_of_type()
	}
	fn expr(&self, i: usize) -> Option<Rc<ExprContextAll<'input>>> where Self:Sized{
		self.child_of_type(i)
	}
}

impl<'input> ExprAndContextAttrs<'input> for ExprAndContext<'input>{}

pub struct ExprAndContextExt<'input>{
	__base:ExprContextExt<'input>,
	pub lhs: Option<Rc<ExprContextAll<'input>>>,
	pub rhs: Option<Rc<ExprContextAll<'input>>>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{ExprAndContextExt<'a>}

impl<'input> LibSLParserContext<'input> for ExprAndContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for ExprAndContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_ExprAnd(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_ExprAnd(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for ExprAndContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_expr }
	//fn type_rule_index() -> usize where Self: Sized { RULE_expr }
}

impl<'input> Borrow<ExprContextExt<'input>> for ExprAndContext<'input>{
	fn borrow(&self) -> &ExprContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<ExprContextExt<'input>> for ExprAndContext<'input>{
	fn borrow_mut(&mut self) -> &mut ExprContextExt<'input> { &mut self.__base }
}

impl<'input> ExprContextAttrs<'input> for ExprAndContext<'input> {}

impl<'input> ExprAndContextExt<'input>{
	fn new(ctx: &dyn ExprContextAttrs<'input>) -> Rc<ExprContextAll<'input>>  {
		Rc::new(
			ExprContextAll::ExprAndContext(
				BaseParserRuleContext::copy_from(ctx,ExprAndContextExt{
        			lhs:None, rhs:None, 
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type ExprDerefContext<'input> = BaseParserRuleContext<'input,ExprDerefContextExt<'input>>;

pub trait ExprDerefContextAttrs<'input>: LibSLParserContext<'input>{
	/// Retrieves first TerminalNode corresponding to token DOT
	/// Returns `None` if there is no child corresponding to token DOT
	fn DOT(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(DOT, 0)
	}
	/// Retrieves first TerminalNode corresponding to token ASTERISK
	/// Returns `None` if there is no child corresponding to token ASTERISK
	fn ASTERISK(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(ASTERISK, 0)
	}
	fn expr(&self) -> Option<Rc<ExprContextAll<'input>>> where Self:Sized{
		self.child_of_type(0)
	}
}

impl<'input> ExprDerefContextAttrs<'input> for ExprDerefContext<'input>{}

pub struct ExprDerefContextExt<'input>{
	__base:ExprContextExt<'input>,
	pub base: Option<Rc<ExprContextAll<'input>>>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{ExprDerefContextExt<'a>}

impl<'input> LibSLParserContext<'input> for ExprDerefContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for ExprDerefContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_ExprDeref(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_ExprDeref(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for ExprDerefContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_expr }
	//fn type_rule_index() -> usize where Self: Sized { RULE_expr }
}

impl<'input> Borrow<ExprContextExt<'input>> for ExprDerefContext<'input>{
	fn borrow(&self) -> &ExprContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<ExprContextExt<'input>> for ExprDerefContext<'input>{
	fn borrow_mut(&mut self) -> &mut ExprContextExt<'input> { &mut self.__base }
}

impl<'input> ExprContextAttrs<'input> for ExprDerefContext<'input> {}

impl<'input> ExprDerefContextExt<'input>{
	fn new(ctx: &dyn ExprContextAttrs<'input>) -> Rc<ExprContextAll<'input>>  {
		Rc::new(
			ExprContextAll::ExprDerefContext(
				BaseParserRuleContext::copy_from(ctx,ExprDerefContextExt{
        			base:None, 
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type ExprUnaryContext<'input> = BaseParserRuleContext<'input,ExprUnaryContextExt<'input>>;

pub trait ExprUnaryContextAttrs<'input>: LibSLParserContext<'input>{
	fn unOp(&self) -> Option<Rc<UnOpContextAll<'input>>> where Self:Sized{
		self.child_of_type(0)
	}
	fn expr(&self) -> Option<Rc<ExprContextAll<'input>>> where Self:Sized{
		self.child_of_type(0)
	}
}

impl<'input> ExprUnaryContextAttrs<'input> for ExprUnaryContext<'input>{}

pub struct ExprUnaryContextExt<'input>{
	__base:ExprContextExt<'input>,
	pub op: Option<Rc<UnOpContextAll<'input>>>,
	pub rhs: Option<Rc<ExprContextAll<'input>>>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{ExprUnaryContextExt<'a>}

impl<'input> LibSLParserContext<'input> for ExprUnaryContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for ExprUnaryContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_ExprUnary(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_ExprUnary(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for ExprUnaryContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_expr }
	//fn type_rule_index() -> usize where Self: Sized { RULE_expr }
}

impl<'input> Borrow<ExprContextExt<'input>> for ExprUnaryContext<'input>{
	fn borrow(&self) -> &ExprContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<ExprContextExt<'input>> for ExprUnaryContext<'input>{
	fn borrow_mut(&mut self) -> &mut ExprContextExt<'input> { &mut self.__base }
}

impl<'input> ExprContextAttrs<'input> for ExprUnaryContext<'input> {}

impl<'input> ExprUnaryContextExt<'input>{
	fn new(ctx: &dyn ExprContextAttrs<'input>) -> Rc<ExprContextAll<'input>>  {
		Rc::new(
			ExprContextAll::ExprUnaryContext(
				BaseParserRuleContext::copy_from(ctx,ExprUnaryContextExt{
        			op:None, rhs:None, 
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type ExprProcCallQualifiedContext<'input> = BaseParserRuleContext<'input,ExprProcCallQualifiedContextExt<'input>>;

pub trait ExprProcCallQualifiedContextAttrs<'input>: LibSLParserContext<'input>{
	/// Retrieves first TerminalNode corresponding to token DOT
	/// Returns `None` if there is no child corresponding to token DOT
	fn DOT(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(DOT, 0)
	}
	/// Retrieves first TerminalNode corresponding to token L_PAREN
	/// Returns `None` if there is no child corresponding to token L_PAREN
	fn L_PAREN(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(L_PAREN, 0)
	}
	/// Retrieves first TerminalNode corresponding to token R_PAREN
	/// Returns `None` if there is no child corresponding to token R_PAREN
	fn R_PAREN(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(R_PAREN, 0)
	}
	fn expr(&self) -> Option<Rc<ExprContextAll<'input>>> where Self:Sized{
		self.child_of_type(0)
	}
	fn ident(&self) -> Option<Rc<IdentContextAll<'input>>> where Self:Sized{
		self.child_of_type(0)
	}
	fn typeArgSpec(&self) -> Option<Rc<TypeArgSpecContextAll<'input>>> where Self:Sized{
		self.child_of_type(0)
	}
	fn exprList(&self) -> Option<Rc<ExprListContextAll<'input>>> where Self:Sized{
		self.child_of_type(0)
	}
	/// Retrieves first TerminalNode corresponding to token COMMA
	/// Returns `None` if there is no child corresponding to token COMMA
	fn COMMA(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(COMMA, 0)
	}
}

impl<'input> ExprProcCallQualifiedContextAttrs<'input> for ExprProcCallQualifiedContext<'input>{}

pub struct ExprProcCallQualifiedContextExt<'input>{
	__base:ExprContextExt<'input>,
	pub base: Option<Rc<ExprContextAll<'input>>>,
	pub name: Option<Rc<IdentContextAll<'input>>>,
	pub typeArgs: Option<Rc<TypeArgSpecContextAll<'input>>>,
	pub args: Option<Rc<ExprListContextAll<'input>>>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{ExprProcCallQualifiedContextExt<'a>}

impl<'input> LibSLParserContext<'input> for ExprProcCallQualifiedContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for ExprProcCallQualifiedContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_ExprProcCallQualified(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_ExprProcCallQualified(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for ExprProcCallQualifiedContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_expr }
	//fn type_rule_index() -> usize where Self: Sized { RULE_expr }
}

impl<'input> Borrow<ExprContextExt<'input>> for ExprProcCallQualifiedContext<'input>{
	fn borrow(&self) -> &ExprContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<ExprContextExt<'input>> for ExprProcCallQualifiedContext<'input>{
	fn borrow_mut(&mut self) -> &mut ExprContextExt<'input> { &mut self.__base }
}

impl<'input> ExprContextAttrs<'input> for ExprProcCallQualifiedContext<'input> {}

impl<'input> ExprProcCallQualifiedContextExt<'input>{
	fn new(ctx: &dyn ExprContextAttrs<'input>) -> Rc<ExprContextAll<'input>>  {
		Rc::new(
			ExprContextAll::ExprProcCallQualifiedContext(
				BaseParserRuleContext::copy_from(ctx,ExprProcCallQualifiedContextExt{
        			base:None, name:None, typeArgs:None, args:None, 
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type ExprBitAndContext<'input> = BaseParserRuleContext<'input,ExprBitAndContextExt<'input>>;

pub trait ExprBitAndContextAttrs<'input>: LibSLParserContext<'input>{
	/// Retrieves first TerminalNode corresponding to token AMP
	/// Returns `None` if there is no child corresponding to token AMP
	fn AMP(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(AMP, 0)
	}
	fn expr_all(&self) ->  Vec<Rc<ExprContextAll<'input>>> where Self:Sized{
		self.children_of_type()
	}
	fn expr(&self, i: usize) -> Option<Rc<ExprContextAll<'input>>> where Self:Sized{
		self.child_of_type(i)
	}
}

impl<'input> ExprBitAndContextAttrs<'input> for ExprBitAndContext<'input>{}

pub struct ExprBitAndContextExt<'input>{
	__base:ExprContextExt<'input>,
	pub lhs: Option<Rc<ExprContextAll<'input>>>,
	pub rhs: Option<Rc<ExprContextAll<'input>>>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{ExprBitAndContextExt<'a>}

impl<'input> LibSLParserContext<'input> for ExprBitAndContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for ExprBitAndContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_ExprBitAnd(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_ExprBitAnd(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for ExprBitAndContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_expr }
	//fn type_rule_index() -> usize where Self: Sized { RULE_expr }
}

impl<'input> Borrow<ExprContextExt<'input>> for ExprBitAndContext<'input>{
	fn borrow(&self) -> &ExprContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<ExprContextExt<'input>> for ExprBitAndContext<'input>{
	fn borrow_mut(&mut self) -> &mut ExprContextExt<'input> { &mut self.__base }
}

impl<'input> ExprContextAttrs<'input> for ExprBitAndContext<'input> {}

impl<'input> ExprBitAndContextExt<'input>{
	fn new(ctx: &dyn ExprContextAttrs<'input>) -> Rc<ExprContextAll<'input>>  {
		Rc::new(
			ExprContextAll::ExprBitAndContext(
				BaseParserRuleContext::copy_from(ctx,ExprBitAndContextExt{
        			lhs:None, rhs:None, 
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

impl<'input, I, H> LibSLParser<'input, I, H>
where
    I: TokenStream<'input, TF = LocalTokenFactory<'input> > + TidAble<'input>,
    H: ErrorStrategy<'input,BaseParserType<'input,I>>
{
	pub fn  expr(&mut self,)
	-> Result<Rc<ExprContextAll<'input>>,ANTLRError> {
		self.expr_rec(0)
	}

	fn expr_rec(&mut self, _p: isize)
	-> Result<Rc<ExprContextAll<'input>>,ANTLRError> {
		let recog = self;
		let _parentctx = recog.ctx.take();
		let _parentState = recog.base.get_state();
		let mut _localctx = ExprContextExt::new(_parentctx.clone(), recog.base.get_state());
		recog.base.enter_recursion_rule(_localctx.clone(), 178, RULE_expr, _p);
	    let mut _localctx: Rc<ExprContextAll> = _localctx;
        let mut _prevctx = _localctx.clone();
		let _startState = 178;
		let mut _la: isize = -1;
		let result: Result<(), ANTLRError> = (|| {
			let mut _alt: isize;
			//recog.base.enter_outer_alt(_localctx.clone(), 1);
			recog.base.enter_outer_alt(None, 1);
			{
			recog.base.set_state(1168);
			recog.err_handler.sync(&mut recog.base)?;
			match  recog.interpreter.adaptive_predict(152,&mut recog.base)? {
				1 =>{
					{
					let mut tmp = ExprParenContextExt::new(&**_localctx);
					recog.ctx = Some(tmp.clone());
					recog.trigger_enter_rule_event();
					_localctx = tmp;
					_prevctx = _localctx.clone();


					recog.base.set_state(1142);
					recog.base.match_token(L_PAREN,&mut recog.err_handler)?;

					/*InvokeRule expr*/
					recog.base.set_state(1143);
					let tmp = recog.expr_rec(0)?;
					if let ExprContextAll::ExprParenContext(ctx) = cast_mut::<_,ExprContextAll >(&mut _localctx){
					ctx.inner = Some(tmp.clone()); } else {unreachable!("cant cast");}  

					recog.base.set_state(1144);
					recog.base.match_token(R_PAREN,&mut recog.err_handler)?;

					}
				}
			,
				2 =>{
					{
					let mut tmp = ExprPrimitiveLitContextExt::new(&**_localctx);
					recog.ctx = Some(tmp.clone());
					recog.trigger_enter_rule_event();
					_localctx = tmp;
					_prevctx = _localctx.clone();
					/*InvokeRule primitiveLit*/
					recog.base.set_state(1146);
					let tmp = recog.primitiveLit()?;
					if let ExprContextAll::ExprPrimitiveLitContext(ctx) = cast_mut::<_,ExprContextAll >(&mut _localctx){
					ctx.lit = Some(tmp.clone()); } else {unreachable!("cant cast");}  

					}
				}
			,
				3 =>{
					{
					let mut tmp = ExprArrayLitContextExt::new(&**_localctx);
					recog.ctx = Some(tmp.clone());
					recog.trigger_enter_rule_event();
					_localctx = tmp;
					_prevctx = _localctx.clone();
					/*InvokeRule arrayLitExpr*/
					recog.base.set_state(1147);
					recog.arrayLitExpr()?;

					}
				}
			,
				4 =>{
					{
					let mut tmp = ExprSetLitContextExt::new(&**_localctx);
					recog.ctx = Some(tmp.clone());
					recog.trigger_enter_rule_event();
					_localctx = tmp;
					_prevctx = _localctx.clone();
					/*InvokeRule setLitExpr*/
					recog.base.set_state(1148);
					recog.setLitExpr()?;

					}
				}
			,
				5 =>{
					{
					let mut tmp = ExprProcCallUnqualifiedContextExt::new(&**_localctx);
					recog.ctx = Some(tmp.clone());
					recog.trigger_enter_rule_event();
					_localctx = tmp;
					_prevctx = _localctx.clone();
					/*InvokeRule ident*/
					recog.base.set_state(1149);
					let tmp = recog.ident()?;
					if let ExprContextAll::ExprProcCallUnqualifiedContext(ctx) = cast_mut::<_,ExprContextAll >(&mut _localctx){
					ctx.name = Some(tmp.clone()); } else {unreachable!("cant cast");}  

					recog.base.set_state(1151);
					recog.err_handler.sync(&mut recog.base)?;
					_la = recog.base.input.la(1);
					if _la==L_ANGLE {
						{
						/*InvokeRule typeArgSpec*/
						recog.base.set_state(1150);
						let tmp = recog.typeArgSpec()?;
						if let ExprContextAll::ExprProcCallUnqualifiedContext(ctx) = cast_mut::<_,ExprContextAll >(&mut _localctx){
						ctx.typeArgs = Some(tmp.clone()); } else {unreachable!("cant cast");}  

						}
					}

					recog.base.set_state(1153);
					recog.base.match_token(L_PAREN,&mut recog.err_handler)?;

					recog.base.set_state(1158);
					recog.err_handler.sync(&mut recog.base)?;
					_la = recog.base.input.la(1);
					if (((_la) & !0x3f) == 0 && ((1usize << _la) & 68682064) != 0) || _la==TILDE || _la==NEW || ((((_la - 69)) & !0x3f) == 0 && ((1usize << (_la - 69)) & 512626737) != 0) {
						{
						/*InvokeRule exprList*/
						recog.base.set_state(1154);
						let tmp = recog.exprList()?;
						if let ExprContextAll::ExprProcCallUnqualifiedContext(ctx) = cast_mut::<_,ExprContextAll >(&mut _localctx){
						ctx.args = Some(tmp.clone()); } else {unreachable!("cant cast");}  

						recog.base.set_state(1156);
						recog.err_handler.sync(&mut recog.base)?;
						_la = recog.base.input.la(1);
						if _la==COMMA {
							{
							recog.base.set_state(1155);
							recog.base.match_token(COMMA,&mut recog.err_handler)?;

							}
						}

						}
					}

					recog.base.set_state(1160);
					recog.base.match_token(R_PAREN,&mut recog.err_handler)?;

					}
				}
			,
				6 =>{
					{
					let mut tmp = ExprActionCallContextExt::new(&**_localctx);
					recog.ctx = Some(tmp.clone());
					recog.trigger_enter_rule_event();
					_localctx = tmp;
					_prevctx = _localctx.clone();
					/*InvokeRule actionCallExpr*/
					recog.base.set_state(1162);
					recog.actionCallExpr()?;

					}
				}
			,
				7 =>{
					{
					let mut tmp = ExprInstantiationContextExt::new(&**_localctx);
					recog.ctx = Some(tmp.clone());
					recog.trigger_enter_rule_event();
					_localctx = tmp;
					_prevctx = _localctx.clone();
					/*InvokeRule instantiationExpr*/
					recog.base.set_state(1163);
					recog.instantiationExpr()?;

					}
				}
			,
				8 =>{
					{
					let mut tmp = ExprNameContextExt::new(&**_localctx);
					recog.ctx = Some(tmp.clone());
					recog.trigger_enter_rule_event();
					_localctx = tmp;
					_prevctx = _localctx.clone();
					/*InvokeRule ident*/
					recog.base.set_state(1164);
					let tmp = recog.ident()?;
					if let ExprContextAll::ExprNameContext(ctx) = cast_mut::<_,ExprContextAll >(&mut _localctx){
					ctx.name = Some(tmp.clone()); } else {unreachable!("cant cast");}  

					}
				}
			,
				9 =>{
					{
					let mut tmp = ExprUnaryContextExt::new(&**_localctx);
					recog.ctx = Some(tmp.clone());
					recog.trigger_enter_rule_event();
					_localctx = tmp;
					_prevctx = _localctx.clone();
					/*InvokeRule unOp*/
					recog.base.set_state(1165);
					let tmp = recog.unOp()?;
					if let ExprContextAll::ExprUnaryContext(ctx) = cast_mut::<_,ExprContextAll >(&mut _localctx){
					ctx.op = Some(tmp.clone()); } else {unreachable!("cant cast");}  

					/*InvokeRule expr*/
					recog.base.set_state(1166);
					let tmp = recog.expr_rec(13)?;
					if let ExprContextAll::ExprUnaryContext(ctx) = cast_mut::<_,ExprContextAll >(&mut _localctx){
					ctx.rhs = Some(tmp.clone()); } else {unreachable!("cant cast");}  

					}
				}

				_ => {}
			}

			let tmp = recog.input.lt(-1).cloned();
			recog.ctx.as_ref().unwrap().set_stop(tmp);
			recog.base.set_state(1246);
			recog.err_handler.sync(&mut recog.base)?;
			_alt = recog.interpreter.adaptive_predict(159,&mut recog.base)?;
			while { _alt!=2 && _alt!=INVALID_ALT } {
				if _alt==1 {
					recog.trigger_exit_rule_event();
					_prevctx = _localctx.clone();
					{
					recog.base.set_state(1244);
					recog.err_handler.sync(&mut recog.base)?;
					match  recog.interpreter.adaptive_predict(158,&mut recog.base)? {
						1 =>{
							{
							/*recRuleLabeledAltStartAction*/
							let mut tmp = ExprMultiplicativeContextExt::new(&**ExprContextExt::new(_parentctx.clone(), _parentState));
							if let ExprContextAll::ExprMultiplicativeContext(ctx) = cast_mut::<_,ExprContextAll >(&mut tmp){
								ctx.lhs = Some(_prevctx.clone());
							} else {unreachable!("cant cast");}
							recog.push_new_recursion_context(tmp.clone(), _startState, RULE_expr);
							_localctx = tmp;
							recog.base.set_state(1170);
							if !({recog.precpred(None, 9)}) {
								Err(FailedPredicateError::new(&mut recog.base, Some("recog.precpred(None, 9)".to_owned()), None))?;
							}
							/*InvokeRule mulBinOp*/
							recog.base.set_state(1171);
							let tmp = recog.mulBinOp()?;
							if let ExprContextAll::ExprMultiplicativeContext(ctx) = cast_mut::<_,ExprContextAll >(&mut _localctx){
							ctx.op = Some(tmp.clone()); } else {unreachable!("cant cast");}  

							/*InvokeRule expr*/
							recog.base.set_state(1172);
							let tmp = recog.expr_rec(10)?;
							if let ExprContextAll::ExprMultiplicativeContext(ctx) = cast_mut::<_,ExprContextAll >(&mut _localctx){
							ctx.rhs = Some(tmp.clone()); } else {unreachable!("cant cast");}  

							}
						}
					,
						2 =>{
							{
							/*recRuleLabeledAltStartAction*/
							let mut tmp = ExprAdditiveContextExt::new(&**ExprContextExt::new(_parentctx.clone(), _parentState));
							if let ExprContextAll::ExprAdditiveContext(ctx) = cast_mut::<_,ExprContextAll >(&mut tmp){
								ctx.lhs = Some(_prevctx.clone());
							} else {unreachable!("cant cast");}
							recog.push_new_recursion_context(tmp.clone(), _startState, RULE_expr);
							_localctx = tmp;
							recog.base.set_state(1174);
							if !({recog.precpred(None, 8)}) {
								Err(FailedPredicateError::new(&mut recog.base, Some("recog.precpred(None, 8)".to_owned()), None))?;
							}
							/*InvokeRule addBinOp*/
							recog.base.set_state(1175);
							let tmp = recog.addBinOp()?;
							if let ExprContextAll::ExprAdditiveContext(ctx) = cast_mut::<_,ExprContextAll >(&mut _localctx){
							ctx.op = Some(tmp.clone()); } else {unreachable!("cant cast");}  

							/*InvokeRule expr*/
							recog.base.set_state(1176);
							let tmp = recog.expr_rec(9)?;
							if let ExprContextAll::ExprAdditiveContext(ctx) = cast_mut::<_,ExprContextAll >(&mut _localctx){
							ctx.rhs = Some(tmp.clone()); } else {unreachable!("cant cast");}  

							}
						}
					,
						3 =>{
							{
							/*recRuleLabeledAltStartAction*/
							let mut tmp = ExprShiftContextExt::new(&**ExprContextExt::new(_parentctx.clone(), _parentState));
							if let ExprContextAll::ExprShiftContext(ctx) = cast_mut::<_,ExprContextAll >(&mut tmp){
								ctx.lhs = Some(_prevctx.clone());
							} else {unreachable!("cant cast");}
							recog.push_new_recursion_context(tmp.clone(), _startState, RULE_expr);
							_localctx = tmp;
							recog.base.set_state(1178);
							if !({recog.precpred(None, 7)}) {
								Err(FailedPredicateError::new(&mut recog.base, Some("recog.precpred(None, 7)".to_owned()), None))?;
							}
							/*InvokeRule bitShiftOp*/
							recog.base.set_state(1179);
							let tmp = recog.bitShiftOp()?;
							if let ExprContextAll::ExprShiftContext(ctx) = cast_mut::<_,ExprContextAll >(&mut _localctx){
							ctx.op = Some(tmp.clone()); } else {unreachable!("cant cast");}  

							/*InvokeRule expr*/
							recog.base.set_state(1180);
							let tmp = recog.expr_rec(8)?;
							if let ExprContextAll::ExprShiftContext(ctx) = cast_mut::<_,ExprContextAll >(&mut _localctx){
							ctx.rhs = Some(tmp.clone()); } else {unreachable!("cant cast");}  

							}
						}
					,
						4 =>{
							{
							/*recRuleLabeledAltStartAction*/
							let mut tmp = ExprBitAndContextExt::new(&**ExprContextExt::new(_parentctx.clone(), _parentState));
							if let ExprContextAll::ExprBitAndContext(ctx) = cast_mut::<_,ExprContextAll >(&mut tmp){
								ctx.lhs = Some(_prevctx.clone());
							} else {unreachable!("cant cast");}
							recog.push_new_recursion_context(tmp.clone(), _startState, RULE_expr);
							_localctx = tmp;
							recog.base.set_state(1182);
							if !({recog.precpred(None, 6)}) {
								Err(FailedPredicateError::new(&mut recog.base, Some("recog.precpred(None, 6)".to_owned()), None))?;
							}
							recog.base.set_state(1183);
							recog.base.match_token(AMP,&mut recog.err_handler)?;

							/*InvokeRule expr*/
							recog.base.set_state(1184);
							let tmp = recog.expr_rec(7)?;
							if let ExprContextAll::ExprBitAndContext(ctx) = cast_mut::<_,ExprContextAll >(&mut _localctx){
							ctx.rhs = Some(tmp.clone()); } else {unreachable!("cant cast");}  

							}
						}
					,
						5 =>{
							{
							/*recRuleLabeledAltStartAction*/
							let mut tmp = ExprBitXorContextExt::new(&**ExprContextExt::new(_parentctx.clone(), _parentState));
							if let ExprContextAll::ExprBitXorContext(ctx) = cast_mut::<_,ExprContextAll >(&mut tmp){
								ctx.lhs = Some(_prevctx.clone());
							} else {unreachable!("cant cast");}
							recog.push_new_recursion_context(tmp.clone(), _startState, RULE_expr);
							_localctx = tmp;
							recog.base.set_state(1185);
							if !({recog.precpred(None, 5)}) {
								Err(FailedPredicateError::new(&mut recog.base, Some("recog.precpred(None, 5)".to_owned()), None))?;
							}
							recog.base.set_state(1186);
							recog.base.match_token(CARET,&mut recog.err_handler)?;

							/*InvokeRule expr*/
							recog.base.set_state(1187);
							let tmp = recog.expr_rec(6)?;
							if let ExprContextAll::ExprBitXorContext(ctx) = cast_mut::<_,ExprContextAll >(&mut _localctx){
							ctx.rhs = Some(tmp.clone()); } else {unreachable!("cant cast");}  

							}
						}
					,
						6 =>{
							{
							/*recRuleLabeledAltStartAction*/
							let mut tmp = ExprBitOrContextExt::new(&**ExprContextExt::new(_parentctx.clone(), _parentState));
							if let ExprContextAll::ExprBitOrContext(ctx) = cast_mut::<_,ExprContextAll >(&mut tmp){
								ctx.lhs = Some(_prevctx.clone());
							} else {unreachable!("cant cast");}
							recog.push_new_recursion_context(tmp.clone(), _startState, RULE_expr);
							_localctx = tmp;
							recog.base.set_state(1188);
							if !({recog.precpred(None, 4)}) {
								Err(FailedPredicateError::new(&mut recog.base, Some("recog.precpred(None, 4)".to_owned()), None))?;
							}
							recog.base.set_state(1189);
							recog.base.match_token(PIPE,&mut recog.err_handler)?;

							/*InvokeRule expr*/
							recog.base.set_state(1190);
							let tmp = recog.expr_rec(5)?;
							if let ExprContextAll::ExprBitOrContext(ctx) = cast_mut::<_,ExprContextAll >(&mut _localctx){
							ctx.rhs = Some(tmp.clone()); } else {unreachable!("cant cast");}  

							}
						}
					,
						7 =>{
							{
							/*recRuleLabeledAltStartAction*/
							let mut tmp = ExprRelationalContextExt::new(&**ExprContextExt::new(_parentctx.clone(), _parentState));
							if let ExprContextAll::ExprRelationalContext(ctx) = cast_mut::<_,ExprContextAll >(&mut tmp){
								ctx.lhs = Some(_prevctx.clone());
							} else {unreachable!("cant cast");}
							recog.push_new_recursion_context(tmp.clone(), _startState, RULE_expr);
							_localctx = tmp;
							recog.base.set_state(1191);
							if !({recog.precpred(None, 3)}) {
								Err(FailedPredicateError::new(&mut recog.base, Some("recog.precpred(None, 3)".to_owned()), None))?;
							}
							/*InvokeRule relOp*/
							recog.base.set_state(1192);
							let tmp = recog.relOp()?;
							if let ExprContextAll::ExprRelationalContext(ctx) = cast_mut::<_,ExprContextAll >(&mut _localctx){
							ctx.op = Some(tmp.clone()); } else {unreachable!("cant cast");}  

							/*InvokeRule expr*/
							recog.base.set_state(1193);
							let tmp = recog.expr_rec(4)?;
							if let ExprContextAll::ExprRelationalContext(ctx) = cast_mut::<_,ExprContextAll >(&mut _localctx){
							ctx.rhs = Some(tmp.clone()); } else {unreachable!("cant cast");}  

							}
						}
					,
						8 =>{
							{
							/*recRuleLabeledAltStartAction*/
							let mut tmp = ExprAndContextExt::new(&**ExprContextExt::new(_parentctx.clone(), _parentState));
							if let ExprContextAll::ExprAndContext(ctx) = cast_mut::<_,ExprContextAll >(&mut tmp){
								ctx.lhs = Some(_prevctx.clone());
							} else {unreachable!("cant cast");}
							recog.push_new_recursion_context(tmp.clone(), _startState, RULE_expr);
							_localctx = tmp;
							recog.base.set_state(1195);
							if !({recog.precpred(None, 2)}) {
								Err(FailedPredicateError::new(&mut recog.base, Some("recog.precpred(None, 2)".to_owned()), None))?;
							}
							recog.base.set_state(1196);
							recog.base.match_token(AMP_AMP,&mut recog.err_handler)?;

							/*InvokeRule expr*/
							recog.base.set_state(1197);
							let tmp = recog.expr_rec(3)?;
							if let ExprContextAll::ExprAndContext(ctx) = cast_mut::<_,ExprContextAll >(&mut _localctx){
							ctx.rhs = Some(tmp.clone()); } else {unreachable!("cant cast");}  

							}
						}
					,
						9 =>{
							{
							/*recRuleLabeledAltStartAction*/
							let mut tmp = ExprOrContextExt::new(&**ExprContextExt::new(_parentctx.clone(), _parentState));
							if let ExprContextAll::ExprOrContext(ctx) = cast_mut::<_,ExprContextAll >(&mut tmp){
								ctx.lhs = Some(_prevctx.clone());
							} else {unreachable!("cant cast");}
							recog.push_new_recursion_context(tmp.clone(), _startState, RULE_expr);
							_localctx = tmp;
							recog.base.set_state(1198);
							if !({recog.precpred(None, 1)}) {
								Err(FailedPredicateError::new(&mut recog.base, Some("recog.precpred(None, 1)".to_owned()), None))?;
							}
							recog.base.set_state(1199);
							recog.base.match_token(PIPE_PIPE,&mut recog.err_handler)?;

							/*InvokeRule expr*/
							recog.base.set_state(1200);
							let tmp = recog.expr_rec(2)?;
							if let ExprContextAll::ExprOrContext(ctx) = cast_mut::<_,ExprContextAll >(&mut _localctx){
							ctx.rhs = Some(tmp.clone()); } else {unreachable!("cant cast");}  

							}
						}
					,
						10 =>{
							{
							/*recRuleLabeledAltStartAction*/
							let mut tmp = ExprPrevContextExt::new(&**ExprContextExt::new(_parentctx.clone(), _parentState));
							if let ExprContextAll::ExprPrevContext(ctx) = cast_mut::<_,ExprContextAll >(&mut tmp){
								ctx.base = Some(_prevctx.clone());
							} else {unreachable!("cant cast");}
							recog.push_new_recursion_context(tmp.clone(), _startState, RULE_expr);
							_localctx = tmp;
							recog.base.set_state(1201);
							if !({recog.precpred(None, 18)}) {
								Err(FailedPredicateError::new(&mut recog.base, Some("recog.precpred(None, 18)".to_owned()), None))?;
							}
							recog.base.set_state(1202);
							recog.base.match_token(QUOTE,&mut recog.err_handler)?;

							}
						}
					,
						11 =>{
							{
							/*recRuleLabeledAltStartAction*/
							let mut tmp = ExprProcCallQualifiedContextExt::new(&**ExprContextExt::new(_parentctx.clone(), _parentState));
							if let ExprContextAll::ExprProcCallQualifiedContext(ctx) = cast_mut::<_,ExprContextAll >(&mut tmp){
								ctx.base = Some(_prevctx.clone());
							} else {unreachable!("cant cast");}
							recog.push_new_recursion_context(tmp.clone(), _startState, RULE_expr);
							_localctx = tmp;
							recog.base.set_state(1203);
							if !({recog.precpred(None, 17)}) {
								Err(FailedPredicateError::new(&mut recog.base, Some("recog.precpred(None, 17)".to_owned()), None))?;
							}
							recog.base.set_state(1204);
							recog.base.match_token(DOT,&mut recog.err_handler)?;

							/*InvokeRule ident*/
							recog.base.set_state(1205);
							let tmp = recog.ident()?;
							if let ExprContextAll::ExprProcCallQualifiedContext(ctx) = cast_mut::<_,ExprContextAll >(&mut _localctx){
							ctx.name = Some(tmp.clone()); } else {unreachable!("cant cast");}  

							recog.base.set_state(1207);
							recog.err_handler.sync(&mut recog.base)?;
							_la = recog.base.input.la(1);
							if _la==L_ANGLE {
								{
								/*InvokeRule typeArgSpec*/
								recog.base.set_state(1206);
								let tmp = recog.typeArgSpec()?;
								if let ExprContextAll::ExprProcCallQualifiedContext(ctx) = cast_mut::<_,ExprContextAll >(&mut _localctx){
								ctx.typeArgs = Some(tmp.clone()); } else {unreachable!("cant cast");}  

								}
							}

							recog.base.set_state(1209);
							recog.base.match_token(L_PAREN,&mut recog.err_handler)?;

							recog.base.set_state(1214);
							recog.err_handler.sync(&mut recog.base)?;
							_la = recog.base.input.la(1);
							if (((_la) & !0x3f) == 0 && ((1usize << _la) & 68682064) != 0) || _la==TILDE || _la==NEW || ((((_la - 69)) & !0x3f) == 0 && ((1usize << (_la - 69)) & 512626737) != 0) {
								{
								/*InvokeRule exprList*/
								recog.base.set_state(1210);
								let tmp = recog.exprList()?;
								if let ExprContextAll::ExprProcCallQualifiedContext(ctx) = cast_mut::<_,ExprContextAll >(&mut _localctx){
								ctx.args = Some(tmp.clone()); } else {unreachable!("cant cast");}  

								recog.base.set_state(1212);
								recog.err_handler.sync(&mut recog.base)?;
								_la = recog.base.input.la(1);
								if _la==COMMA {
									{
									recog.base.set_state(1211);
									recog.base.match_token(COMMA,&mut recog.err_handler)?;

									}
								}

								}
							}

							recog.base.set_state(1216);
							recog.base.match_token(R_PAREN,&mut recog.err_handler)?;

							}
						}
					,
						12 =>{
							{
							/*recRuleLabeledAltStartAction*/
							let mut tmp = ExprFieldContextExt::new(&**ExprContextExt::new(_parentctx.clone(), _parentState));
							if let ExprContextAll::ExprFieldContext(ctx) = cast_mut::<_,ExprContextAll >(&mut tmp){
								ctx.base = Some(_prevctx.clone());
							} else {unreachable!("cant cast");}
							recog.push_new_recursion_context(tmp.clone(), _startState, RULE_expr);
							_localctx = tmp;
							recog.base.set_state(1218);
							if !({recog.precpred(None, 16)}) {
								Err(FailedPredicateError::new(&mut recog.base, Some("recog.precpred(None, 16)".to_owned()), None))?;
							}
							recog.base.set_state(1219);
							recog.base.match_token(DOT,&mut recog.err_handler)?;

							/*InvokeRule ident*/
							recog.base.set_state(1220);
							let tmp = recog.ident()?;
							if let ExprContextAll::ExprFieldContext(ctx) = cast_mut::<_,ExprContextAll >(&mut _localctx){
							ctx.field = Some(tmp.clone()); } else {unreachable!("cant cast");}  

							}
						}
					,
						13 =>{
							{
							/*recRuleLabeledAltStartAction*/
							let mut tmp = ExprDerefContextExt::new(&**ExprContextExt::new(_parentctx.clone(), _parentState));
							if let ExprContextAll::ExprDerefContext(ctx) = cast_mut::<_,ExprContextAll >(&mut tmp){
								ctx.base = Some(_prevctx.clone());
							} else {unreachable!("cant cast");}
							recog.push_new_recursion_context(tmp.clone(), _startState, RULE_expr);
							_localctx = tmp;
							recog.base.set_state(1221);
							if !({recog.precpred(None, 15)}) {
								Err(FailedPredicateError::new(&mut recog.base, Some("recog.precpred(None, 15)".to_owned()), None))?;
							}
							recog.base.set_state(1222);
							recog.base.match_token(DOT,&mut recog.err_handler)?;

							recog.base.set_state(1223);
							recog.base.match_token(ASTERISK,&mut recog.err_handler)?;

							}
						}
					,
						14 =>{
							{
							/*recRuleLabeledAltStartAction*/
							let mut tmp = ExprIndexContextExt::new(&**ExprContextExt::new(_parentctx.clone(), _parentState));
							if let ExprContextAll::ExprIndexContext(ctx) = cast_mut::<_,ExprContextAll >(&mut tmp){
								ctx.base = Some(_prevctx.clone());
							} else {unreachable!("cant cast");}
							recog.push_new_recursion_context(tmp.clone(), _startState, RULE_expr);
							_localctx = tmp;
							recog.base.set_state(1224);
							if !({recog.precpred(None, 14)}) {
								Err(FailedPredicateError::new(&mut recog.base, Some("recog.precpred(None, 14)".to_owned()), None))?;
							}
							recog.base.set_state(1225);
							recog.base.match_token(L_BRACKET,&mut recog.err_handler)?;

							/*InvokeRule expr*/
							recog.base.set_state(1226);
							let tmp = recog.expr_rec(0)?;
							if let ExprContextAll::ExprIndexContext(ctx) = cast_mut::<_,ExprContextAll >(&mut _localctx){
							ctx.index = Some(tmp.clone()); } else {unreachable!("cant cast");}  

							recog.base.set_state(1227);
							recog.base.match_token(R_BRACKET,&mut recog.err_handler)?;

							}
						}
					,
						15 =>{
							{
							/*recRuleLabeledAltStartAction*/
							let mut tmp = ExprHasConceptContextExt::new(&**ExprContextExt::new(_parentctx.clone(), _parentState));
							if let ExprContextAll::ExprHasConceptContext(ctx) = cast_mut::<_,ExprContextAll >(&mut tmp){
								ctx.lhs = Some(_prevctx.clone());
							} else {unreachable!("cant cast");}
							recog.push_new_recursion_context(tmp.clone(), _startState, RULE_expr);
							_localctx = tmp;
							recog.base.set_state(1229);
							if !({recog.precpred(None, 12)}) {
								Err(FailedPredicateError::new(&mut recog.base, Some("recog.precpred(None, 12)".to_owned()), None))?;
							}
							recog.base.set_state(1231);
							recog.err_handler.sync(&mut recog.base)?;
							_la = recog.base.input.la(1);
							if _la==BANG {
								{
								recog.base.set_state(1230);
								let tmp = recog.base.match_token(BANG,&mut recog.err_handler)?;
								if let ExprContextAll::ExprHasConceptContext(ctx) = cast_mut::<_,ExprContextAll >(&mut _localctx){
								ctx.not = Some(tmp.clone()); } else {unreachable!("cant cast");}  

								}
							}

							recog.base.set_state(1233);
							recog.base.match_token(HAS,&mut recog.err_handler)?;

							/*InvokeRule ident*/
							recog.base.set_state(1234);
							let tmp = recog.ident()?;
							if let ExprContextAll::ExprHasConceptContext(ctx) = cast_mut::<_,ExprContextAll >(&mut _localctx){
							ctx.concept = Some(tmp.clone()); } else {unreachable!("cant cast");}  

							}
						}
					,
						16 =>{
							{
							/*recRuleLabeledAltStartAction*/
							let mut tmp = ExprTypeComparisonContextExt::new(&**ExprContextExt::new(_parentctx.clone(), _parentState));
							if let ExprContextAll::ExprTypeComparisonContext(ctx) = cast_mut::<_,ExprContextAll >(&mut tmp){
								ctx.lhs = Some(_prevctx.clone());
							} else {unreachable!("cant cast");}
							recog.push_new_recursion_context(tmp.clone(), _startState, RULE_expr);
							_localctx = tmp;
							recog.base.set_state(1235);
							if !({recog.precpred(None, 11)}) {
								Err(FailedPredicateError::new(&mut recog.base, Some("recog.precpred(None, 11)".to_owned()), None))?;
							}
							recog.base.set_state(1237);
							recog.err_handler.sync(&mut recog.base)?;
							_la = recog.base.input.la(1);
							if _la==BANG {
								{
								recog.base.set_state(1236);
								let tmp = recog.base.match_token(BANG,&mut recog.err_handler)?;
								if let ExprContextAll::ExprTypeComparisonContext(ctx) = cast_mut::<_,ExprContextAll >(&mut _localctx){
								ctx.not = Some(tmp.clone()); } else {unreachable!("cant cast");}  

								}
							}

							recog.base.set_state(1239);
							recog.base.match_token(IS,&mut recog.err_handler)?;

							/*InvokeRule typeExpr*/
							recog.base.set_state(1240);
							let tmp = recog.typeExpr_rec(0)?;
							if let ExprContextAll::ExprTypeComparisonContext(ctx) = cast_mut::<_,ExprContextAll >(&mut _localctx){
							ctx.r#type = Some(tmp.clone()); } else {unreachable!("cant cast");}  

							}
						}
					,
						17 =>{
							{
							/*recRuleLabeledAltStartAction*/
							let mut tmp = ExprCastContextExt::new(&**ExprContextExt::new(_parentctx.clone(), _parentState));
							if let ExprContextAll::ExprCastContext(ctx) = cast_mut::<_,ExprContextAll >(&mut tmp){
								ctx.lhs = Some(_prevctx.clone());
							} else {unreachable!("cant cast");}
							recog.push_new_recursion_context(tmp.clone(), _startState, RULE_expr);
							_localctx = tmp;
							recog.base.set_state(1241);
							if !({recog.precpred(None, 10)}) {
								Err(FailedPredicateError::new(&mut recog.base, Some("recog.precpred(None, 10)".to_owned()), None))?;
							}
							recog.base.set_state(1242);
							recog.base.match_token(AS,&mut recog.err_handler)?;

							/*InvokeRule typeExpr*/
							recog.base.set_state(1243);
							let tmp = recog.typeExpr_rec(0)?;
							if let ExprContextAll::ExprCastContext(ctx) = cast_mut::<_,ExprContextAll >(&mut _localctx){
							ctx.r#type = Some(tmp.clone()); } else {unreachable!("cant cast");}  

							}
						}

						_ => {}
					}
					} 
				}
				recog.base.set_state(1248);
				recog.err_handler.sync(&mut recog.base)?;
				_alt = recog.interpreter.adaptive_predict(159,&mut recog.base)?;
			}
			}
			Ok(())
		})();
		match result {
		Ok(_) => {},
        Err(e @ ANTLRError::FallThrough(_)) => return Err(e),
		Err(ref re)=>{
			//_localctx.exception = re;
			recog.err_handler.report_error(&mut recog.base, re);
	        recog.err_handler.recover(&mut recog.base, re)?;}
		}
		recog.base.unroll_recursion_context(_parentctx);

		Ok(_localctx)
	}
}
//------------------- unOp ----------------
#[derive(Debug)]
pub enum UnOpContextAll<'input>{
	UnOpNegContext(UnOpNegContext<'input>),
	UnOpPlusContext(UnOpPlusContext<'input>),
	UnOpNotContext(UnOpNotContext<'input>),
	UnOpBitNotContext(UnOpBitNotContext<'input>),
Error(UnOpContext<'input>)
}
antlr_rust::tid!{UnOpContextAll<'a>}

impl<'input> antlr_rust::parser_rule_context::DerefSeal for UnOpContextAll<'input>{}

impl<'input> LibSLParserContext<'input> for UnOpContextAll<'input>{}

impl<'input> Deref for UnOpContextAll<'input>{
	type Target = dyn UnOpContextAttrs<'input> + 'input;
	fn deref(&self) -> &Self::Target{
		use UnOpContextAll::*;
		match self{
			UnOpNegContext(inner) => inner,
			UnOpPlusContext(inner) => inner,
			UnOpNotContext(inner) => inner,
			UnOpBitNotContext(inner) => inner,
Error(inner) => inner
		}
	}
}
impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for UnOpContextAll<'input>{
    fn enter(&self, listener: &mut (dyn LibSLParserListener<'input> + 'a)) { self.deref().enter(listener) }
    fn exit(&self, listener: &mut (dyn LibSLParserListener<'input> + 'a)) { self.deref().exit(listener) }
}



pub type UnOpContext<'input> = BaseParserRuleContext<'input,UnOpContextExt<'input>>;

#[derive(Clone)]
pub struct UnOpContextExt<'input>{
ph:PhantomData<&'input str>
}

impl<'input> LibSLParserContext<'input> for UnOpContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for UnOpContext<'input>{
}

impl<'input> CustomRuleContext<'input> for UnOpContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_unOp }
	//fn type_rule_index() -> usize where Self: Sized { RULE_unOp }
}
antlr_rust::tid!{UnOpContextExt<'a>}

impl<'input> UnOpContextExt<'input>{
	fn new(parent: Option<Rc<dyn LibSLParserContext<'input> + 'input > >, invoking_state: isize) -> Rc<UnOpContextAll<'input>> {
		Rc::new(
		UnOpContextAll::Error(
			BaseParserRuleContext::new_parser_ctx(parent, invoking_state,UnOpContextExt{
				ph:PhantomData
			}),
		)
		)
	}
}

pub trait UnOpContextAttrs<'input>: LibSLParserContext<'input> + BorrowMut<UnOpContextExt<'input>>{


}

impl<'input> UnOpContextAttrs<'input> for UnOpContext<'input>{}

pub type UnOpNegContext<'input> = BaseParserRuleContext<'input,UnOpNegContextExt<'input>>;

pub trait UnOpNegContextAttrs<'input>: LibSLParserContext<'input>{
	/// Retrieves first TerminalNode corresponding to token MINUS
	/// Returns `None` if there is no child corresponding to token MINUS
	fn MINUS(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(MINUS, 0)
	}
}

impl<'input> UnOpNegContextAttrs<'input> for UnOpNegContext<'input>{}

pub struct UnOpNegContextExt<'input>{
	__base:UnOpContextExt<'input>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{UnOpNegContextExt<'a>}

impl<'input> LibSLParserContext<'input> for UnOpNegContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for UnOpNegContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_UnOpNeg(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_UnOpNeg(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for UnOpNegContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_unOp }
	//fn type_rule_index() -> usize where Self: Sized { RULE_unOp }
}

impl<'input> Borrow<UnOpContextExt<'input>> for UnOpNegContext<'input>{
	fn borrow(&self) -> &UnOpContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<UnOpContextExt<'input>> for UnOpNegContext<'input>{
	fn borrow_mut(&mut self) -> &mut UnOpContextExt<'input> { &mut self.__base }
}

impl<'input> UnOpContextAttrs<'input> for UnOpNegContext<'input> {}

impl<'input> UnOpNegContextExt<'input>{
	fn new(ctx: &dyn UnOpContextAttrs<'input>) -> Rc<UnOpContextAll<'input>>  {
		Rc::new(
			UnOpContextAll::UnOpNegContext(
				BaseParserRuleContext::copy_from(ctx,UnOpNegContextExt{
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type UnOpPlusContext<'input> = BaseParserRuleContext<'input,UnOpPlusContextExt<'input>>;

pub trait UnOpPlusContextAttrs<'input>: LibSLParserContext<'input>{
	/// Retrieves first TerminalNode corresponding to token PLUS
	/// Returns `None` if there is no child corresponding to token PLUS
	fn PLUS(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(PLUS, 0)
	}
}

impl<'input> UnOpPlusContextAttrs<'input> for UnOpPlusContext<'input>{}

pub struct UnOpPlusContextExt<'input>{
	__base:UnOpContextExt<'input>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{UnOpPlusContextExt<'a>}

impl<'input> LibSLParserContext<'input> for UnOpPlusContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for UnOpPlusContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_UnOpPlus(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_UnOpPlus(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for UnOpPlusContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_unOp }
	//fn type_rule_index() -> usize where Self: Sized { RULE_unOp }
}

impl<'input> Borrow<UnOpContextExt<'input>> for UnOpPlusContext<'input>{
	fn borrow(&self) -> &UnOpContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<UnOpContextExt<'input>> for UnOpPlusContext<'input>{
	fn borrow_mut(&mut self) -> &mut UnOpContextExt<'input> { &mut self.__base }
}

impl<'input> UnOpContextAttrs<'input> for UnOpPlusContext<'input> {}

impl<'input> UnOpPlusContextExt<'input>{
	fn new(ctx: &dyn UnOpContextAttrs<'input>) -> Rc<UnOpContextAll<'input>>  {
		Rc::new(
			UnOpContextAll::UnOpPlusContext(
				BaseParserRuleContext::copy_from(ctx,UnOpPlusContextExt{
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type UnOpNotContext<'input> = BaseParserRuleContext<'input,UnOpNotContextExt<'input>>;

pub trait UnOpNotContextAttrs<'input>: LibSLParserContext<'input>{
	/// Retrieves first TerminalNode corresponding to token BANG
	/// Returns `None` if there is no child corresponding to token BANG
	fn BANG(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(BANG, 0)
	}
}

impl<'input> UnOpNotContextAttrs<'input> for UnOpNotContext<'input>{}

pub struct UnOpNotContextExt<'input>{
	__base:UnOpContextExt<'input>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{UnOpNotContextExt<'a>}

impl<'input> LibSLParserContext<'input> for UnOpNotContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for UnOpNotContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_UnOpNot(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_UnOpNot(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for UnOpNotContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_unOp }
	//fn type_rule_index() -> usize where Self: Sized { RULE_unOp }
}

impl<'input> Borrow<UnOpContextExt<'input>> for UnOpNotContext<'input>{
	fn borrow(&self) -> &UnOpContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<UnOpContextExt<'input>> for UnOpNotContext<'input>{
	fn borrow_mut(&mut self) -> &mut UnOpContextExt<'input> { &mut self.__base }
}

impl<'input> UnOpContextAttrs<'input> for UnOpNotContext<'input> {}

impl<'input> UnOpNotContextExt<'input>{
	fn new(ctx: &dyn UnOpContextAttrs<'input>) -> Rc<UnOpContextAll<'input>>  {
		Rc::new(
			UnOpContextAll::UnOpNotContext(
				BaseParserRuleContext::copy_from(ctx,UnOpNotContextExt{
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type UnOpBitNotContext<'input> = BaseParserRuleContext<'input,UnOpBitNotContextExt<'input>>;

pub trait UnOpBitNotContextAttrs<'input>: LibSLParserContext<'input>{
	/// Retrieves first TerminalNode corresponding to token TILDE
	/// Returns `None` if there is no child corresponding to token TILDE
	fn TILDE(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(TILDE, 0)
	}
}

impl<'input> UnOpBitNotContextAttrs<'input> for UnOpBitNotContext<'input>{}

pub struct UnOpBitNotContextExt<'input>{
	__base:UnOpContextExt<'input>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{UnOpBitNotContextExt<'a>}

impl<'input> LibSLParserContext<'input> for UnOpBitNotContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for UnOpBitNotContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_UnOpBitNot(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_UnOpBitNot(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for UnOpBitNotContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_unOp }
	//fn type_rule_index() -> usize where Self: Sized { RULE_unOp }
}

impl<'input> Borrow<UnOpContextExt<'input>> for UnOpBitNotContext<'input>{
	fn borrow(&self) -> &UnOpContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<UnOpContextExt<'input>> for UnOpBitNotContext<'input>{
	fn borrow_mut(&mut self) -> &mut UnOpContextExt<'input> { &mut self.__base }
}

impl<'input> UnOpContextAttrs<'input> for UnOpBitNotContext<'input> {}

impl<'input> UnOpBitNotContextExt<'input>{
	fn new(ctx: &dyn UnOpContextAttrs<'input>) -> Rc<UnOpContextAll<'input>>  {
		Rc::new(
			UnOpContextAll::UnOpBitNotContext(
				BaseParserRuleContext::copy_from(ctx,UnOpBitNotContextExt{
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

impl<'input, I, H> LibSLParser<'input, I, H>
where
    I: TokenStream<'input, TF = LocalTokenFactory<'input> > + TidAble<'input>,
    H: ErrorStrategy<'input,BaseParserType<'input,I>>
{
	pub fn unOp(&mut self,)
	-> Result<Rc<UnOpContextAll<'input>>,ANTLRError> {
		let mut recog = self;
		let _parentctx = recog.ctx.take();
		let mut _localctx = UnOpContextExt::new(_parentctx.clone(), recog.base.get_state());
        recog.base.enter_rule(_localctx.clone(), 180, RULE_unOp);
        let mut _localctx: Rc<UnOpContextAll> = _localctx;
		let result: Result<(), ANTLRError> = (|| {

			recog.base.set_state(1253);
			recog.err_handler.sync(&mut recog.base)?;
			match recog.base.input.la(1) {
			 PLUS 
				=> {
					let tmp = UnOpPlusContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 1);
					_localctx = tmp;
					{
					recog.base.set_state(1249);
					recog.base.match_token(PLUS,&mut recog.err_handler)?;

					}
				}

			 MINUS 
				=> {
					let tmp = UnOpNegContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 2);
					_localctx = tmp;
					{
					recog.base.set_state(1250);
					recog.base.match_token(MINUS,&mut recog.err_handler)?;

					}
				}

			 TILDE 
				=> {
					let tmp = UnOpBitNotContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 3);
					_localctx = tmp;
					{
					recog.base.set_state(1251);
					recog.base.match_token(TILDE,&mut recog.err_handler)?;

					}
				}

			 BANG 
				=> {
					let tmp = UnOpNotContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 4);
					_localctx = tmp;
					{
					recog.base.set_state(1252);
					recog.base.match_token(BANG,&mut recog.err_handler)?;

					}
				}

				_ => Err(ANTLRError::NoAltError(NoViableAltError::new(&mut recog.base)))?
			}
			Ok(())
		})();
		match result {
		Ok(_)=>{},
        Err(e @ ANTLRError::FallThrough(_)) => return Err(e),
		Err(ref re) => {
				//_localctx.exception = re;
				recog.err_handler.report_error(&mut recog.base, re);
				recog.err_handler.recover(&mut recog.base, re)?;
			}
		}
		recog.base.exit_rule();

		Ok(_localctx)
	}
}
//------------------- mulBinOp ----------------
#[derive(Debug)]
pub enum MulBinOpContextAll<'input>{
	BinOpMulContext(BinOpMulContext<'input>),
	BinOpModContext(BinOpModContext<'input>),
	BinOpDivContext(BinOpDivContext<'input>),
Error(MulBinOpContext<'input>)
}
antlr_rust::tid!{MulBinOpContextAll<'a>}

impl<'input> antlr_rust::parser_rule_context::DerefSeal for MulBinOpContextAll<'input>{}

impl<'input> LibSLParserContext<'input> for MulBinOpContextAll<'input>{}

impl<'input> Deref for MulBinOpContextAll<'input>{
	type Target = dyn MulBinOpContextAttrs<'input> + 'input;
	fn deref(&self) -> &Self::Target{
		use MulBinOpContextAll::*;
		match self{
			BinOpMulContext(inner) => inner,
			BinOpModContext(inner) => inner,
			BinOpDivContext(inner) => inner,
Error(inner) => inner
		}
	}
}
impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for MulBinOpContextAll<'input>{
    fn enter(&self, listener: &mut (dyn LibSLParserListener<'input> + 'a)) { self.deref().enter(listener) }
    fn exit(&self, listener: &mut (dyn LibSLParserListener<'input> + 'a)) { self.deref().exit(listener) }
}



pub type MulBinOpContext<'input> = BaseParserRuleContext<'input,MulBinOpContextExt<'input>>;

#[derive(Clone)]
pub struct MulBinOpContextExt<'input>{
ph:PhantomData<&'input str>
}

impl<'input> LibSLParserContext<'input> for MulBinOpContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for MulBinOpContext<'input>{
}

impl<'input> CustomRuleContext<'input> for MulBinOpContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_mulBinOp }
	//fn type_rule_index() -> usize where Self: Sized { RULE_mulBinOp }
}
antlr_rust::tid!{MulBinOpContextExt<'a>}

impl<'input> MulBinOpContextExt<'input>{
	fn new(parent: Option<Rc<dyn LibSLParserContext<'input> + 'input > >, invoking_state: isize) -> Rc<MulBinOpContextAll<'input>> {
		Rc::new(
		MulBinOpContextAll::Error(
			BaseParserRuleContext::new_parser_ctx(parent, invoking_state,MulBinOpContextExt{
				ph:PhantomData
			}),
		)
		)
	}
}

pub trait MulBinOpContextAttrs<'input>: LibSLParserContext<'input> + BorrowMut<MulBinOpContextExt<'input>>{


}

impl<'input> MulBinOpContextAttrs<'input> for MulBinOpContext<'input>{}

pub type BinOpMulContext<'input> = BaseParserRuleContext<'input,BinOpMulContextExt<'input>>;

pub trait BinOpMulContextAttrs<'input>: LibSLParserContext<'input>{
	/// Retrieves first TerminalNode corresponding to token ASTERISK
	/// Returns `None` if there is no child corresponding to token ASTERISK
	fn ASTERISK(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(ASTERISK, 0)
	}
}

impl<'input> BinOpMulContextAttrs<'input> for BinOpMulContext<'input>{}

pub struct BinOpMulContextExt<'input>{
	__base:MulBinOpContextExt<'input>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{BinOpMulContextExt<'a>}

impl<'input> LibSLParserContext<'input> for BinOpMulContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for BinOpMulContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_BinOpMul(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_BinOpMul(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for BinOpMulContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_mulBinOp }
	//fn type_rule_index() -> usize where Self: Sized { RULE_mulBinOp }
}

impl<'input> Borrow<MulBinOpContextExt<'input>> for BinOpMulContext<'input>{
	fn borrow(&self) -> &MulBinOpContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<MulBinOpContextExt<'input>> for BinOpMulContext<'input>{
	fn borrow_mut(&mut self) -> &mut MulBinOpContextExt<'input> { &mut self.__base }
}

impl<'input> MulBinOpContextAttrs<'input> for BinOpMulContext<'input> {}

impl<'input> BinOpMulContextExt<'input>{
	fn new(ctx: &dyn MulBinOpContextAttrs<'input>) -> Rc<MulBinOpContextAll<'input>>  {
		Rc::new(
			MulBinOpContextAll::BinOpMulContext(
				BaseParserRuleContext::copy_from(ctx,BinOpMulContextExt{
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type BinOpModContext<'input> = BaseParserRuleContext<'input,BinOpModContextExt<'input>>;

pub trait BinOpModContextAttrs<'input>: LibSLParserContext<'input>{
	/// Retrieves first TerminalNode corresponding to token PERCENT
	/// Returns `None` if there is no child corresponding to token PERCENT
	fn PERCENT(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(PERCENT, 0)
	}
}

impl<'input> BinOpModContextAttrs<'input> for BinOpModContext<'input>{}

pub struct BinOpModContextExt<'input>{
	__base:MulBinOpContextExt<'input>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{BinOpModContextExt<'a>}

impl<'input> LibSLParserContext<'input> for BinOpModContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for BinOpModContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_BinOpMod(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_BinOpMod(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for BinOpModContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_mulBinOp }
	//fn type_rule_index() -> usize where Self: Sized { RULE_mulBinOp }
}

impl<'input> Borrow<MulBinOpContextExt<'input>> for BinOpModContext<'input>{
	fn borrow(&self) -> &MulBinOpContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<MulBinOpContextExt<'input>> for BinOpModContext<'input>{
	fn borrow_mut(&mut self) -> &mut MulBinOpContextExt<'input> { &mut self.__base }
}

impl<'input> MulBinOpContextAttrs<'input> for BinOpModContext<'input> {}

impl<'input> BinOpModContextExt<'input>{
	fn new(ctx: &dyn MulBinOpContextAttrs<'input>) -> Rc<MulBinOpContextAll<'input>>  {
		Rc::new(
			MulBinOpContextAll::BinOpModContext(
				BaseParserRuleContext::copy_from(ctx,BinOpModContextExt{
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type BinOpDivContext<'input> = BaseParserRuleContext<'input,BinOpDivContextExt<'input>>;

pub trait BinOpDivContextAttrs<'input>: LibSLParserContext<'input>{
	/// Retrieves first TerminalNode corresponding to token SLASH
	/// Returns `None` if there is no child corresponding to token SLASH
	fn SLASH(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(SLASH, 0)
	}
}

impl<'input> BinOpDivContextAttrs<'input> for BinOpDivContext<'input>{}

pub struct BinOpDivContextExt<'input>{
	__base:MulBinOpContextExt<'input>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{BinOpDivContextExt<'a>}

impl<'input> LibSLParserContext<'input> for BinOpDivContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for BinOpDivContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_BinOpDiv(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_BinOpDiv(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for BinOpDivContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_mulBinOp }
	//fn type_rule_index() -> usize where Self: Sized { RULE_mulBinOp }
}

impl<'input> Borrow<MulBinOpContextExt<'input>> for BinOpDivContext<'input>{
	fn borrow(&self) -> &MulBinOpContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<MulBinOpContextExt<'input>> for BinOpDivContext<'input>{
	fn borrow_mut(&mut self) -> &mut MulBinOpContextExt<'input> { &mut self.__base }
}

impl<'input> MulBinOpContextAttrs<'input> for BinOpDivContext<'input> {}

impl<'input> BinOpDivContextExt<'input>{
	fn new(ctx: &dyn MulBinOpContextAttrs<'input>) -> Rc<MulBinOpContextAll<'input>>  {
		Rc::new(
			MulBinOpContextAll::BinOpDivContext(
				BaseParserRuleContext::copy_from(ctx,BinOpDivContextExt{
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

impl<'input, I, H> LibSLParser<'input, I, H>
where
    I: TokenStream<'input, TF = LocalTokenFactory<'input> > + TidAble<'input>,
    H: ErrorStrategy<'input,BaseParserType<'input,I>>
{
	pub fn mulBinOp(&mut self,)
	-> Result<Rc<MulBinOpContextAll<'input>>,ANTLRError> {
		let mut recog = self;
		let _parentctx = recog.ctx.take();
		let mut _localctx = MulBinOpContextExt::new(_parentctx.clone(), recog.base.get_state());
        recog.base.enter_rule(_localctx.clone(), 182, RULE_mulBinOp);
        let mut _localctx: Rc<MulBinOpContextAll> = _localctx;
		let result: Result<(), ANTLRError> = (|| {

			recog.base.set_state(1258);
			recog.err_handler.sync(&mut recog.base)?;
			match recog.base.input.la(1) {
			 ASTERISK 
				=> {
					let tmp = BinOpMulContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 1);
					_localctx = tmp;
					{
					recog.base.set_state(1255);
					recog.base.match_token(ASTERISK,&mut recog.err_handler)?;

					}
				}

			 SLASH 
				=> {
					let tmp = BinOpDivContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 2);
					_localctx = tmp;
					{
					recog.base.set_state(1256);
					recog.base.match_token(SLASH,&mut recog.err_handler)?;

					}
				}

			 PERCENT 
				=> {
					let tmp = BinOpModContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 3);
					_localctx = tmp;
					{
					recog.base.set_state(1257);
					recog.base.match_token(PERCENT,&mut recog.err_handler)?;

					}
				}

				_ => Err(ANTLRError::NoAltError(NoViableAltError::new(&mut recog.base)))?
			}
			Ok(())
		})();
		match result {
		Ok(_)=>{},
        Err(e @ ANTLRError::FallThrough(_)) => return Err(e),
		Err(ref re) => {
				//_localctx.exception = re;
				recog.err_handler.report_error(&mut recog.base, re);
				recog.err_handler.recover(&mut recog.base, re)?;
			}
		}
		recog.base.exit_rule();

		Ok(_localctx)
	}
}
//------------------- addBinOp ----------------
#[derive(Debug)]
pub enum AddBinOpContextAll<'input>{
	BinOpSubContext(BinOpSubContext<'input>),
	BinOpAddContext(BinOpAddContext<'input>),
Error(AddBinOpContext<'input>)
}
antlr_rust::tid!{AddBinOpContextAll<'a>}

impl<'input> antlr_rust::parser_rule_context::DerefSeal for AddBinOpContextAll<'input>{}

impl<'input> LibSLParserContext<'input> for AddBinOpContextAll<'input>{}

impl<'input> Deref for AddBinOpContextAll<'input>{
	type Target = dyn AddBinOpContextAttrs<'input> + 'input;
	fn deref(&self) -> &Self::Target{
		use AddBinOpContextAll::*;
		match self{
			BinOpSubContext(inner) => inner,
			BinOpAddContext(inner) => inner,
Error(inner) => inner
		}
	}
}
impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for AddBinOpContextAll<'input>{
    fn enter(&self, listener: &mut (dyn LibSLParserListener<'input> + 'a)) { self.deref().enter(listener) }
    fn exit(&self, listener: &mut (dyn LibSLParserListener<'input> + 'a)) { self.deref().exit(listener) }
}



pub type AddBinOpContext<'input> = BaseParserRuleContext<'input,AddBinOpContextExt<'input>>;

#[derive(Clone)]
pub struct AddBinOpContextExt<'input>{
ph:PhantomData<&'input str>
}

impl<'input> LibSLParserContext<'input> for AddBinOpContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for AddBinOpContext<'input>{
}

impl<'input> CustomRuleContext<'input> for AddBinOpContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_addBinOp }
	//fn type_rule_index() -> usize where Self: Sized { RULE_addBinOp }
}
antlr_rust::tid!{AddBinOpContextExt<'a>}

impl<'input> AddBinOpContextExt<'input>{
	fn new(parent: Option<Rc<dyn LibSLParserContext<'input> + 'input > >, invoking_state: isize) -> Rc<AddBinOpContextAll<'input>> {
		Rc::new(
		AddBinOpContextAll::Error(
			BaseParserRuleContext::new_parser_ctx(parent, invoking_state,AddBinOpContextExt{
				ph:PhantomData
			}),
		)
		)
	}
}

pub trait AddBinOpContextAttrs<'input>: LibSLParserContext<'input> + BorrowMut<AddBinOpContextExt<'input>>{


}

impl<'input> AddBinOpContextAttrs<'input> for AddBinOpContext<'input>{}

pub type BinOpSubContext<'input> = BaseParserRuleContext<'input,BinOpSubContextExt<'input>>;

pub trait BinOpSubContextAttrs<'input>: LibSLParserContext<'input>{
	/// Retrieves first TerminalNode corresponding to token MINUS
	/// Returns `None` if there is no child corresponding to token MINUS
	fn MINUS(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(MINUS, 0)
	}
}

impl<'input> BinOpSubContextAttrs<'input> for BinOpSubContext<'input>{}

pub struct BinOpSubContextExt<'input>{
	__base:AddBinOpContextExt<'input>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{BinOpSubContextExt<'a>}

impl<'input> LibSLParserContext<'input> for BinOpSubContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for BinOpSubContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_BinOpSub(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_BinOpSub(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for BinOpSubContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_addBinOp }
	//fn type_rule_index() -> usize where Self: Sized { RULE_addBinOp }
}

impl<'input> Borrow<AddBinOpContextExt<'input>> for BinOpSubContext<'input>{
	fn borrow(&self) -> &AddBinOpContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<AddBinOpContextExt<'input>> for BinOpSubContext<'input>{
	fn borrow_mut(&mut self) -> &mut AddBinOpContextExt<'input> { &mut self.__base }
}

impl<'input> AddBinOpContextAttrs<'input> for BinOpSubContext<'input> {}

impl<'input> BinOpSubContextExt<'input>{
	fn new(ctx: &dyn AddBinOpContextAttrs<'input>) -> Rc<AddBinOpContextAll<'input>>  {
		Rc::new(
			AddBinOpContextAll::BinOpSubContext(
				BaseParserRuleContext::copy_from(ctx,BinOpSubContextExt{
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type BinOpAddContext<'input> = BaseParserRuleContext<'input,BinOpAddContextExt<'input>>;

pub trait BinOpAddContextAttrs<'input>: LibSLParserContext<'input>{
	/// Retrieves first TerminalNode corresponding to token PLUS
	/// Returns `None` if there is no child corresponding to token PLUS
	fn PLUS(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(PLUS, 0)
	}
}

impl<'input> BinOpAddContextAttrs<'input> for BinOpAddContext<'input>{}

pub struct BinOpAddContextExt<'input>{
	__base:AddBinOpContextExt<'input>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{BinOpAddContextExt<'a>}

impl<'input> LibSLParserContext<'input> for BinOpAddContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for BinOpAddContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_BinOpAdd(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_BinOpAdd(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for BinOpAddContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_addBinOp }
	//fn type_rule_index() -> usize where Self: Sized { RULE_addBinOp }
}

impl<'input> Borrow<AddBinOpContextExt<'input>> for BinOpAddContext<'input>{
	fn borrow(&self) -> &AddBinOpContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<AddBinOpContextExt<'input>> for BinOpAddContext<'input>{
	fn borrow_mut(&mut self) -> &mut AddBinOpContextExt<'input> { &mut self.__base }
}

impl<'input> AddBinOpContextAttrs<'input> for BinOpAddContext<'input> {}

impl<'input> BinOpAddContextExt<'input>{
	fn new(ctx: &dyn AddBinOpContextAttrs<'input>) -> Rc<AddBinOpContextAll<'input>>  {
		Rc::new(
			AddBinOpContextAll::BinOpAddContext(
				BaseParserRuleContext::copy_from(ctx,BinOpAddContextExt{
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

impl<'input, I, H> LibSLParser<'input, I, H>
where
    I: TokenStream<'input, TF = LocalTokenFactory<'input> > + TidAble<'input>,
    H: ErrorStrategy<'input,BaseParserType<'input,I>>
{
	pub fn addBinOp(&mut self,)
	-> Result<Rc<AddBinOpContextAll<'input>>,ANTLRError> {
		let mut recog = self;
		let _parentctx = recog.ctx.take();
		let mut _localctx = AddBinOpContextExt::new(_parentctx.clone(), recog.base.get_state());
        recog.base.enter_rule(_localctx.clone(), 184, RULE_addBinOp);
        let mut _localctx: Rc<AddBinOpContextAll> = _localctx;
		let result: Result<(), ANTLRError> = (|| {

			recog.base.set_state(1262);
			recog.err_handler.sync(&mut recog.base)?;
			match recog.base.input.la(1) {
			 PLUS 
				=> {
					let tmp = BinOpAddContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 1);
					_localctx = tmp;
					{
					recog.base.set_state(1260);
					recog.base.match_token(PLUS,&mut recog.err_handler)?;

					}
				}

			 MINUS 
				=> {
					let tmp = BinOpSubContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 2);
					_localctx = tmp;
					{
					recog.base.set_state(1261);
					recog.base.match_token(MINUS,&mut recog.err_handler)?;

					}
				}

				_ => Err(ANTLRError::NoAltError(NoViableAltError::new(&mut recog.base)))?
			}
			Ok(())
		})();
		match result {
		Ok(_)=>{},
        Err(e @ ANTLRError::FallThrough(_)) => return Err(e),
		Err(ref re) => {
				//_localctx.exception = re;
				recog.err_handler.report_error(&mut recog.base, re);
				recog.err_handler.recover(&mut recog.base, re)?;
			}
		}
		recog.base.exit_rule();

		Ok(_localctx)
	}
}
//------------------- bitShiftOp ----------------
#[derive(Debug)]
pub enum BitShiftOpContextAll<'input>{
	BinOpArithmeticLeftContext(BinOpArithmeticLeftContext<'input>),
	BinOpLogicalLeftContext(BinOpLogicalLeftContext<'input>),
	BinOpLogicalRightContext(BinOpLogicalRightContext<'input>),
	BinOpArithmeticRightContext(BinOpArithmeticRightContext<'input>),
Error(BitShiftOpContext<'input>)
}
antlr_rust::tid!{BitShiftOpContextAll<'a>}

impl<'input> antlr_rust::parser_rule_context::DerefSeal for BitShiftOpContextAll<'input>{}

impl<'input> LibSLParserContext<'input> for BitShiftOpContextAll<'input>{}

impl<'input> Deref for BitShiftOpContextAll<'input>{
	type Target = dyn BitShiftOpContextAttrs<'input> + 'input;
	fn deref(&self) -> &Self::Target{
		use BitShiftOpContextAll::*;
		match self{
			BinOpArithmeticLeftContext(inner) => inner,
			BinOpLogicalLeftContext(inner) => inner,
			BinOpLogicalRightContext(inner) => inner,
			BinOpArithmeticRightContext(inner) => inner,
Error(inner) => inner
		}
	}
}
impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for BitShiftOpContextAll<'input>{
    fn enter(&self, listener: &mut (dyn LibSLParserListener<'input> + 'a)) { self.deref().enter(listener) }
    fn exit(&self, listener: &mut (dyn LibSLParserListener<'input> + 'a)) { self.deref().exit(listener) }
}



pub type BitShiftOpContext<'input> = BaseParserRuleContext<'input,BitShiftOpContextExt<'input>>;

#[derive(Clone)]
pub struct BitShiftOpContextExt<'input>{
ph:PhantomData<&'input str>
}

impl<'input> LibSLParserContext<'input> for BitShiftOpContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for BitShiftOpContext<'input>{
}

impl<'input> CustomRuleContext<'input> for BitShiftOpContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_bitShiftOp }
	//fn type_rule_index() -> usize where Self: Sized { RULE_bitShiftOp }
}
antlr_rust::tid!{BitShiftOpContextExt<'a>}

impl<'input> BitShiftOpContextExt<'input>{
	fn new(parent: Option<Rc<dyn LibSLParserContext<'input> + 'input > >, invoking_state: isize) -> Rc<BitShiftOpContextAll<'input>> {
		Rc::new(
		BitShiftOpContextAll::Error(
			BaseParserRuleContext::new_parser_ctx(parent, invoking_state,BitShiftOpContextExt{
				ph:PhantomData
			}),
		)
		)
	}
}

pub trait BitShiftOpContextAttrs<'input>: LibSLParserContext<'input> + BorrowMut<BitShiftOpContextExt<'input>>{


}

impl<'input> BitShiftOpContextAttrs<'input> for BitShiftOpContext<'input>{}

pub type BinOpArithmeticLeftContext<'input> = BaseParserRuleContext<'input,BinOpArithmeticLeftContextExt<'input>>;

pub trait BinOpArithmeticLeftContextAttrs<'input>: LibSLParserContext<'input>{
	/// Retrieves all `TerminalNode`s corresponding to token L_ANGLE in current rule
	fn L_ANGLE_all(&self) -> Vec<Rc<TerminalNode<'input,LibSLParserContextType>>>  where Self:Sized{
		self.get_tokens(L_ANGLE)
	}
	/// Retrieves 'i's TerminalNode corresponding to token L_ANGLE, starting from 0.
	/// Returns `None` if number of children corresponding to token L_ANGLE is less or equal than `i`.
	fn L_ANGLE(&self, i: usize) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(L_ANGLE, i)
	}
}

impl<'input> BinOpArithmeticLeftContextAttrs<'input> for BinOpArithmeticLeftContext<'input>{}

pub struct BinOpArithmeticLeftContextExt<'input>{
	__base:BitShiftOpContextExt<'input>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{BinOpArithmeticLeftContextExt<'a>}

impl<'input> LibSLParserContext<'input> for BinOpArithmeticLeftContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for BinOpArithmeticLeftContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_BinOpArithmeticLeft(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_BinOpArithmeticLeft(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for BinOpArithmeticLeftContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_bitShiftOp }
	//fn type_rule_index() -> usize where Self: Sized { RULE_bitShiftOp }
}

impl<'input> Borrow<BitShiftOpContextExt<'input>> for BinOpArithmeticLeftContext<'input>{
	fn borrow(&self) -> &BitShiftOpContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<BitShiftOpContextExt<'input>> for BinOpArithmeticLeftContext<'input>{
	fn borrow_mut(&mut self) -> &mut BitShiftOpContextExt<'input> { &mut self.__base }
}

impl<'input> BitShiftOpContextAttrs<'input> for BinOpArithmeticLeftContext<'input> {}

impl<'input> BinOpArithmeticLeftContextExt<'input>{
	fn new(ctx: &dyn BitShiftOpContextAttrs<'input>) -> Rc<BitShiftOpContextAll<'input>>  {
		Rc::new(
			BitShiftOpContextAll::BinOpArithmeticLeftContext(
				BaseParserRuleContext::copy_from(ctx,BinOpArithmeticLeftContextExt{
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type BinOpLogicalLeftContext<'input> = BaseParserRuleContext<'input,BinOpLogicalLeftContextExt<'input>>;

pub trait BinOpLogicalLeftContextAttrs<'input>: LibSLParserContext<'input>{
	/// Retrieves all `TerminalNode`s corresponding to token L_ANGLE in current rule
	fn L_ANGLE_all(&self) -> Vec<Rc<TerminalNode<'input,LibSLParserContextType>>>  where Self:Sized{
		self.get_tokens(L_ANGLE)
	}
	/// Retrieves 'i's TerminalNode corresponding to token L_ANGLE, starting from 0.
	/// Returns `None` if number of children corresponding to token L_ANGLE is less or equal than `i`.
	fn L_ANGLE(&self, i: usize) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(L_ANGLE, i)
	}
}

impl<'input> BinOpLogicalLeftContextAttrs<'input> for BinOpLogicalLeftContext<'input>{}

pub struct BinOpLogicalLeftContextExt<'input>{
	__base:BitShiftOpContextExt<'input>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{BinOpLogicalLeftContextExt<'a>}

impl<'input> LibSLParserContext<'input> for BinOpLogicalLeftContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for BinOpLogicalLeftContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_BinOpLogicalLeft(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_BinOpLogicalLeft(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for BinOpLogicalLeftContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_bitShiftOp }
	//fn type_rule_index() -> usize where Self: Sized { RULE_bitShiftOp }
}

impl<'input> Borrow<BitShiftOpContextExt<'input>> for BinOpLogicalLeftContext<'input>{
	fn borrow(&self) -> &BitShiftOpContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<BitShiftOpContextExt<'input>> for BinOpLogicalLeftContext<'input>{
	fn borrow_mut(&mut self) -> &mut BitShiftOpContextExt<'input> { &mut self.__base }
}

impl<'input> BitShiftOpContextAttrs<'input> for BinOpLogicalLeftContext<'input> {}

impl<'input> BinOpLogicalLeftContextExt<'input>{
	fn new(ctx: &dyn BitShiftOpContextAttrs<'input>) -> Rc<BitShiftOpContextAll<'input>>  {
		Rc::new(
			BitShiftOpContextAll::BinOpLogicalLeftContext(
				BaseParserRuleContext::copy_from(ctx,BinOpLogicalLeftContextExt{
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type BinOpLogicalRightContext<'input> = BaseParserRuleContext<'input,BinOpLogicalRightContextExt<'input>>;

pub trait BinOpLogicalRightContextAttrs<'input>: LibSLParserContext<'input>{
	/// Retrieves all `TerminalNode`s corresponding to token R_ANGLE in current rule
	fn R_ANGLE_all(&self) -> Vec<Rc<TerminalNode<'input,LibSLParserContextType>>>  where Self:Sized{
		self.get_tokens(R_ANGLE)
	}
	/// Retrieves 'i's TerminalNode corresponding to token R_ANGLE, starting from 0.
	/// Returns `None` if number of children corresponding to token R_ANGLE is less or equal than `i`.
	fn R_ANGLE(&self, i: usize) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(R_ANGLE, i)
	}
}

impl<'input> BinOpLogicalRightContextAttrs<'input> for BinOpLogicalRightContext<'input>{}

pub struct BinOpLogicalRightContextExt<'input>{
	__base:BitShiftOpContextExt<'input>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{BinOpLogicalRightContextExt<'a>}

impl<'input> LibSLParserContext<'input> for BinOpLogicalRightContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for BinOpLogicalRightContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_BinOpLogicalRight(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_BinOpLogicalRight(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for BinOpLogicalRightContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_bitShiftOp }
	//fn type_rule_index() -> usize where Self: Sized { RULE_bitShiftOp }
}

impl<'input> Borrow<BitShiftOpContextExt<'input>> for BinOpLogicalRightContext<'input>{
	fn borrow(&self) -> &BitShiftOpContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<BitShiftOpContextExt<'input>> for BinOpLogicalRightContext<'input>{
	fn borrow_mut(&mut self) -> &mut BitShiftOpContextExt<'input> { &mut self.__base }
}

impl<'input> BitShiftOpContextAttrs<'input> for BinOpLogicalRightContext<'input> {}

impl<'input> BinOpLogicalRightContextExt<'input>{
	fn new(ctx: &dyn BitShiftOpContextAttrs<'input>) -> Rc<BitShiftOpContextAll<'input>>  {
		Rc::new(
			BitShiftOpContextAll::BinOpLogicalRightContext(
				BaseParserRuleContext::copy_from(ctx,BinOpLogicalRightContextExt{
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type BinOpArithmeticRightContext<'input> = BaseParserRuleContext<'input,BinOpArithmeticRightContextExt<'input>>;

pub trait BinOpArithmeticRightContextAttrs<'input>: LibSLParserContext<'input>{
	/// Retrieves all `TerminalNode`s corresponding to token R_ANGLE in current rule
	fn R_ANGLE_all(&self) -> Vec<Rc<TerminalNode<'input,LibSLParserContextType>>>  where Self:Sized{
		self.get_tokens(R_ANGLE)
	}
	/// Retrieves 'i's TerminalNode corresponding to token R_ANGLE, starting from 0.
	/// Returns `None` if number of children corresponding to token R_ANGLE is less or equal than `i`.
	fn R_ANGLE(&self, i: usize) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(R_ANGLE, i)
	}
}

impl<'input> BinOpArithmeticRightContextAttrs<'input> for BinOpArithmeticRightContext<'input>{}

pub struct BinOpArithmeticRightContextExt<'input>{
	__base:BitShiftOpContextExt<'input>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{BinOpArithmeticRightContextExt<'a>}

impl<'input> LibSLParserContext<'input> for BinOpArithmeticRightContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for BinOpArithmeticRightContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_BinOpArithmeticRight(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_BinOpArithmeticRight(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for BinOpArithmeticRightContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_bitShiftOp }
	//fn type_rule_index() -> usize where Self: Sized { RULE_bitShiftOp }
}

impl<'input> Borrow<BitShiftOpContextExt<'input>> for BinOpArithmeticRightContext<'input>{
	fn borrow(&self) -> &BitShiftOpContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<BitShiftOpContextExt<'input>> for BinOpArithmeticRightContext<'input>{
	fn borrow_mut(&mut self) -> &mut BitShiftOpContextExt<'input> { &mut self.__base }
}

impl<'input> BitShiftOpContextAttrs<'input> for BinOpArithmeticRightContext<'input> {}

impl<'input> BinOpArithmeticRightContextExt<'input>{
	fn new(ctx: &dyn BitShiftOpContextAttrs<'input>) -> Rc<BitShiftOpContextAll<'input>>  {
		Rc::new(
			BitShiftOpContextAll::BinOpArithmeticRightContext(
				BaseParserRuleContext::copy_from(ctx,BinOpArithmeticRightContextExt{
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

impl<'input, I, H> LibSLParser<'input, I, H>
where
    I: TokenStream<'input, TF = LocalTokenFactory<'input> > + TidAble<'input>,
    H: ErrorStrategy<'input,BaseParserType<'input,I>>
{
	pub fn bitShiftOp(&mut self,)
	-> Result<Rc<BitShiftOpContextAll<'input>>,ANTLRError> {
		let mut recog = self;
		let _parentctx = recog.ctx.take();
		let mut _localctx = BitShiftOpContextExt::new(_parentctx.clone(), recog.base.get_state());
        recog.base.enter_rule(_localctx.clone(), 186, RULE_bitShiftOp);
        let mut _localctx: Rc<BitShiftOpContextAll> = _localctx;
		let result: Result<(), ANTLRError> = (|| {

			recog.base.set_state(1274);
			recog.err_handler.sync(&mut recog.base)?;
			match  recog.interpreter.adaptive_predict(163,&mut recog.base)? {
				1 =>{
					let tmp = BinOpLogicalLeftContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 1);
					_localctx = tmp;
					{
					recog.base.set_state(1264);
					recog.base.match_token(L_ANGLE,&mut recog.err_handler)?;

					recog.base.set_state(1265);
					recog.base.match_token(L_ANGLE,&mut recog.err_handler)?;

					recog.base.set_state(1266);
					recog.base.match_token(L_ANGLE,&mut recog.err_handler)?;

					}
				}
			,
				2 =>{
					let tmp = BinOpLogicalRightContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 2);
					_localctx = tmp;
					{
					recog.base.set_state(1267);
					recog.base.match_token(R_ANGLE,&mut recog.err_handler)?;

					recog.base.set_state(1268);
					recog.base.match_token(R_ANGLE,&mut recog.err_handler)?;

					recog.base.set_state(1269);
					recog.base.match_token(R_ANGLE,&mut recog.err_handler)?;

					}
				}
			,
				3 =>{
					let tmp = BinOpArithmeticLeftContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 3);
					_localctx = tmp;
					{
					recog.base.set_state(1270);
					recog.base.match_token(L_ANGLE,&mut recog.err_handler)?;

					recog.base.set_state(1271);
					recog.base.match_token(L_ANGLE,&mut recog.err_handler)?;

					}
				}
			,
				4 =>{
					let tmp = BinOpArithmeticRightContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 4);
					_localctx = tmp;
					{
					recog.base.set_state(1272);
					recog.base.match_token(R_ANGLE,&mut recog.err_handler)?;

					recog.base.set_state(1273);
					recog.base.match_token(R_ANGLE,&mut recog.err_handler)?;

					}
				}

				_ => {}
			}
			Ok(())
		})();
		match result {
		Ok(_)=>{},
        Err(e @ ANTLRError::FallThrough(_)) => return Err(e),
		Err(ref re) => {
				//_localctx.exception = re;
				recog.err_handler.report_error(&mut recog.base, re);
				recog.err_handler.recover(&mut recog.base, re)?;
			}
		}
		recog.base.exit_rule();

		Ok(_localctx)
	}
}
//------------------- relOp ----------------
#[derive(Debug)]
pub enum RelOpContextAll<'input>{
	BinOpGreaterEqualsContext(BinOpGreaterEqualsContext<'input>),
	BinOpLessEqualsContext(BinOpLessEqualsContext<'input>),
	BinOpEqualsContext(BinOpEqualsContext<'input>),
	BinOpInContext(BinOpInContext<'input>),
	BinOpGreaterContext(BinOpGreaterContext<'input>),
	BinOpLessContext(BinOpLessContext<'input>),
	BinOpNotEqualsContext(BinOpNotEqualsContext<'input>),
Error(RelOpContext<'input>)
}
antlr_rust::tid!{RelOpContextAll<'a>}

impl<'input> antlr_rust::parser_rule_context::DerefSeal for RelOpContextAll<'input>{}

impl<'input> LibSLParserContext<'input> for RelOpContextAll<'input>{}

impl<'input> Deref for RelOpContextAll<'input>{
	type Target = dyn RelOpContextAttrs<'input> + 'input;
	fn deref(&self) -> &Self::Target{
		use RelOpContextAll::*;
		match self{
			BinOpGreaterEqualsContext(inner) => inner,
			BinOpLessEqualsContext(inner) => inner,
			BinOpEqualsContext(inner) => inner,
			BinOpInContext(inner) => inner,
			BinOpGreaterContext(inner) => inner,
			BinOpLessContext(inner) => inner,
			BinOpNotEqualsContext(inner) => inner,
Error(inner) => inner
		}
	}
}
impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for RelOpContextAll<'input>{
    fn enter(&self, listener: &mut (dyn LibSLParserListener<'input> + 'a)) { self.deref().enter(listener) }
    fn exit(&self, listener: &mut (dyn LibSLParserListener<'input> + 'a)) { self.deref().exit(listener) }
}



pub type RelOpContext<'input> = BaseParserRuleContext<'input,RelOpContextExt<'input>>;

#[derive(Clone)]
pub struct RelOpContextExt<'input>{
ph:PhantomData<&'input str>
}

impl<'input> LibSLParserContext<'input> for RelOpContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for RelOpContext<'input>{
}

impl<'input> CustomRuleContext<'input> for RelOpContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_relOp }
	//fn type_rule_index() -> usize where Self: Sized { RULE_relOp }
}
antlr_rust::tid!{RelOpContextExt<'a>}

impl<'input> RelOpContextExt<'input>{
	fn new(parent: Option<Rc<dyn LibSLParserContext<'input> + 'input > >, invoking_state: isize) -> Rc<RelOpContextAll<'input>> {
		Rc::new(
		RelOpContextAll::Error(
			BaseParserRuleContext::new_parser_ctx(parent, invoking_state,RelOpContextExt{
				ph:PhantomData
			}),
		)
		)
	}
}

pub trait RelOpContextAttrs<'input>: LibSLParserContext<'input> + BorrowMut<RelOpContextExt<'input>>{


}

impl<'input> RelOpContextAttrs<'input> for RelOpContext<'input>{}

pub type BinOpGreaterEqualsContext<'input> = BaseParserRuleContext<'input,BinOpGreaterEqualsContextExt<'input>>;

pub trait BinOpGreaterEqualsContextAttrs<'input>: LibSLParserContext<'input>{
	/// Retrieves first TerminalNode corresponding to token R_ANGLE_EQ
	/// Returns `None` if there is no child corresponding to token R_ANGLE_EQ
	fn R_ANGLE_EQ(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(R_ANGLE_EQ, 0)
	}
}

impl<'input> BinOpGreaterEqualsContextAttrs<'input> for BinOpGreaterEqualsContext<'input>{}

pub struct BinOpGreaterEqualsContextExt<'input>{
	__base:RelOpContextExt<'input>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{BinOpGreaterEqualsContextExt<'a>}

impl<'input> LibSLParserContext<'input> for BinOpGreaterEqualsContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for BinOpGreaterEqualsContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_BinOpGreaterEquals(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_BinOpGreaterEquals(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for BinOpGreaterEqualsContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_relOp }
	//fn type_rule_index() -> usize where Self: Sized { RULE_relOp }
}

impl<'input> Borrow<RelOpContextExt<'input>> for BinOpGreaterEqualsContext<'input>{
	fn borrow(&self) -> &RelOpContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<RelOpContextExt<'input>> for BinOpGreaterEqualsContext<'input>{
	fn borrow_mut(&mut self) -> &mut RelOpContextExt<'input> { &mut self.__base }
}

impl<'input> RelOpContextAttrs<'input> for BinOpGreaterEqualsContext<'input> {}

impl<'input> BinOpGreaterEqualsContextExt<'input>{
	fn new(ctx: &dyn RelOpContextAttrs<'input>) -> Rc<RelOpContextAll<'input>>  {
		Rc::new(
			RelOpContextAll::BinOpGreaterEqualsContext(
				BaseParserRuleContext::copy_from(ctx,BinOpGreaterEqualsContextExt{
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type BinOpLessEqualsContext<'input> = BaseParserRuleContext<'input,BinOpLessEqualsContextExt<'input>>;

pub trait BinOpLessEqualsContextAttrs<'input>: LibSLParserContext<'input>{
	/// Retrieves first TerminalNode corresponding to token L_ANGLE_EQ
	/// Returns `None` if there is no child corresponding to token L_ANGLE_EQ
	fn L_ANGLE_EQ(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(L_ANGLE_EQ, 0)
	}
}

impl<'input> BinOpLessEqualsContextAttrs<'input> for BinOpLessEqualsContext<'input>{}

pub struct BinOpLessEqualsContextExt<'input>{
	__base:RelOpContextExt<'input>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{BinOpLessEqualsContextExt<'a>}

impl<'input> LibSLParserContext<'input> for BinOpLessEqualsContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for BinOpLessEqualsContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_BinOpLessEquals(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_BinOpLessEquals(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for BinOpLessEqualsContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_relOp }
	//fn type_rule_index() -> usize where Self: Sized { RULE_relOp }
}

impl<'input> Borrow<RelOpContextExt<'input>> for BinOpLessEqualsContext<'input>{
	fn borrow(&self) -> &RelOpContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<RelOpContextExt<'input>> for BinOpLessEqualsContext<'input>{
	fn borrow_mut(&mut self) -> &mut RelOpContextExt<'input> { &mut self.__base }
}

impl<'input> RelOpContextAttrs<'input> for BinOpLessEqualsContext<'input> {}

impl<'input> BinOpLessEqualsContextExt<'input>{
	fn new(ctx: &dyn RelOpContextAttrs<'input>) -> Rc<RelOpContextAll<'input>>  {
		Rc::new(
			RelOpContextAll::BinOpLessEqualsContext(
				BaseParserRuleContext::copy_from(ctx,BinOpLessEqualsContextExt{
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type BinOpEqualsContext<'input> = BaseParserRuleContext<'input,BinOpEqualsContextExt<'input>>;

pub trait BinOpEqualsContextAttrs<'input>: LibSLParserContext<'input>{
	/// Retrieves first TerminalNode corresponding to token EQ_EQ
	/// Returns `None` if there is no child corresponding to token EQ_EQ
	fn EQ_EQ(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(EQ_EQ, 0)
	}
}

impl<'input> BinOpEqualsContextAttrs<'input> for BinOpEqualsContext<'input>{}

pub struct BinOpEqualsContextExt<'input>{
	__base:RelOpContextExt<'input>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{BinOpEqualsContextExt<'a>}

impl<'input> LibSLParserContext<'input> for BinOpEqualsContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for BinOpEqualsContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_BinOpEquals(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_BinOpEquals(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for BinOpEqualsContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_relOp }
	//fn type_rule_index() -> usize where Self: Sized { RULE_relOp }
}

impl<'input> Borrow<RelOpContextExt<'input>> for BinOpEqualsContext<'input>{
	fn borrow(&self) -> &RelOpContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<RelOpContextExt<'input>> for BinOpEqualsContext<'input>{
	fn borrow_mut(&mut self) -> &mut RelOpContextExt<'input> { &mut self.__base }
}

impl<'input> RelOpContextAttrs<'input> for BinOpEqualsContext<'input> {}

impl<'input> BinOpEqualsContextExt<'input>{
	fn new(ctx: &dyn RelOpContextAttrs<'input>) -> Rc<RelOpContextAll<'input>>  {
		Rc::new(
			RelOpContextAll::BinOpEqualsContext(
				BaseParserRuleContext::copy_from(ctx,BinOpEqualsContextExt{
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type BinOpInContext<'input> = BaseParserRuleContext<'input,BinOpInContextExt<'input>>;

pub trait BinOpInContextAttrs<'input>: LibSLParserContext<'input>{
	/// Retrieves first TerminalNode corresponding to token IN
	/// Returns `None` if there is no child corresponding to token IN
	fn IN(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(IN, 0)
	}
	/// Retrieves first TerminalNode corresponding to token BANG
	/// Returns `None` if there is no child corresponding to token BANG
	fn BANG(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(BANG, 0)
	}
}

impl<'input> BinOpInContextAttrs<'input> for BinOpInContext<'input>{}

pub struct BinOpInContextExt<'input>{
	__base:RelOpContextExt<'input>,
	pub not: Option<TokenType<'input>>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{BinOpInContextExt<'a>}

impl<'input> LibSLParserContext<'input> for BinOpInContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for BinOpInContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_BinOpIn(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_BinOpIn(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for BinOpInContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_relOp }
	//fn type_rule_index() -> usize where Self: Sized { RULE_relOp }
}

impl<'input> Borrow<RelOpContextExt<'input>> for BinOpInContext<'input>{
	fn borrow(&self) -> &RelOpContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<RelOpContextExt<'input>> for BinOpInContext<'input>{
	fn borrow_mut(&mut self) -> &mut RelOpContextExt<'input> { &mut self.__base }
}

impl<'input> RelOpContextAttrs<'input> for BinOpInContext<'input> {}

impl<'input> BinOpInContextExt<'input>{
	fn new(ctx: &dyn RelOpContextAttrs<'input>) -> Rc<RelOpContextAll<'input>>  {
		Rc::new(
			RelOpContextAll::BinOpInContext(
				BaseParserRuleContext::copy_from(ctx,BinOpInContextExt{
					not:None, 
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type BinOpGreaterContext<'input> = BaseParserRuleContext<'input,BinOpGreaterContextExt<'input>>;

pub trait BinOpGreaterContextAttrs<'input>: LibSLParserContext<'input>{
	/// Retrieves first TerminalNode corresponding to token R_ANGLE
	/// Returns `None` if there is no child corresponding to token R_ANGLE
	fn R_ANGLE(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(R_ANGLE, 0)
	}
}

impl<'input> BinOpGreaterContextAttrs<'input> for BinOpGreaterContext<'input>{}

pub struct BinOpGreaterContextExt<'input>{
	__base:RelOpContextExt<'input>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{BinOpGreaterContextExt<'a>}

impl<'input> LibSLParserContext<'input> for BinOpGreaterContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for BinOpGreaterContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_BinOpGreater(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_BinOpGreater(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for BinOpGreaterContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_relOp }
	//fn type_rule_index() -> usize where Self: Sized { RULE_relOp }
}

impl<'input> Borrow<RelOpContextExt<'input>> for BinOpGreaterContext<'input>{
	fn borrow(&self) -> &RelOpContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<RelOpContextExt<'input>> for BinOpGreaterContext<'input>{
	fn borrow_mut(&mut self) -> &mut RelOpContextExt<'input> { &mut self.__base }
}

impl<'input> RelOpContextAttrs<'input> for BinOpGreaterContext<'input> {}

impl<'input> BinOpGreaterContextExt<'input>{
	fn new(ctx: &dyn RelOpContextAttrs<'input>) -> Rc<RelOpContextAll<'input>>  {
		Rc::new(
			RelOpContextAll::BinOpGreaterContext(
				BaseParserRuleContext::copy_from(ctx,BinOpGreaterContextExt{
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type BinOpLessContext<'input> = BaseParserRuleContext<'input,BinOpLessContextExt<'input>>;

pub trait BinOpLessContextAttrs<'input>: LibSLParserContext<'input>{
	/// Retrieves first TerminalNode corresponding to token L_ANGLE
	/// Returns `None` if there is no child corresponding to token L_ANGLE
	fn L_ANGLE(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(L_ANGLE, 0)
	}
}

impl<'input> BinOpLessContextAttrs<'input> for BinOpLessContext<'input>{}

pub struct BinOpLessContextExt<'input>{
	__base:RelOpContextExt<'input>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{BinOpLessContextExt<'a>}

impl<'input> LibSLParserContext<'input> for BinOpLessContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for BinOpLessContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_BinOpLess(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_BinOpLess(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for BinOpLessContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_relOp }
	//fn type_rule_index() -> usize where Self: Sized { RULE_relOp }
}

impl<'input> Borrow<RelOpContextExt<'input>> for BinOpLessContext<'input>{
	fn borrow(&self) -> &RelOpContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<RelOpContextExt<'input>> for BinOpLessContext<'input>{
	fn borrow_mut(&mut self) -> &mut RelOpContextExt<'input> { &mut self.__base }
}

impl<'input> RelOpContextAttrs<'input> for BinOpLessContext<'input> {}

impl<'input> BinOpLessContextExt<'input>{
	fn new(ctx: &dyn RelOpContextAttrs<'input>) -> Rc<RelOpContextAll<'input>>  {
		Rc::new(
			RelOpContextAll::BinOpLessContext(
				BaseParserRuleContext::copy_from(ctx,BinOpLessContextExt{
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type BinOpNotEqualsContext<'input> = BaseParserRuleContext<'input,BinOpNotEqualsContextExt<'input>>;

pub trait BinOpNotEqualsContextAttrs<'input>: LibSLParserContext<'input>{
	/// Retrieves first TerminalNode corresponding to token BANG_EQ
	/// Returns `None` if there is no child corresponding to token BANG_EQ
	fn BANG_EQ(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(BANG_EQ, 0)
	}
}

impl<'input> BinOpNotEqualsContextAttrs<'input> for BinOpNotEqualsContext<'input>{}

pub struct BinOpNotEqualsContextExt<'input>{
	__base:RelOpContextExt<'input>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{BinOpNotEqualsContextExt<'a>}

impl<'input> LibSLParserContext<'input> for BinOpNotEqualsContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for BinOpNotEqualsContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_BinOpNotEquals(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_BinOpNotEquals(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for BinOpNotEqualsContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_relOp }
	//fn type_rule_index() -> usize where Self: Sized { RULE_relOp }
}

impl<'input> Borrow<RelOpContextExt<'input>> for BinOpNotEqualsContext<'input>{
	fn borrow(&self) -> &RelOpContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<RelOpContextExt<'input>> for BinOpNotEqualsContext<'input>{
	fn borrow_mut(&mut self) -> &mut RelOpContextExt<'input> { &mut self.__base }
}

impl<'input> RelOpContextAttrs<'input> for BinOpNotEqualsContext<'input> {}

impl<'input> BinOpNotEqualsContextExt<'input>{
	fn new(ctx: &dyn RelOpContextAttrs<'input>) -> Rc<RelOpContextAll<'input>>  {
		Rc::new(
			RelOpContextAll::BinOpNotEqualsContext(
				BaseParserRuleContext::copy_from(ctx,BinOpNotEqualsContextExt{
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

impl<'input, I, H> LibSLParser<'input, I, H>
where
    I: TokenStream<'input, TF = LocalTokenFactory<'input> > + TidAble<'input>,
    H: ErrorStrategy<'input,BaseParserType<'input,I>>
{
	pub fn relOp(&mut self,)
	-> Result<Rc<RelOpContextAll<'input>>,ANTLRError> {
		let mut recog = self;
		let _parentctx = recog.ctx.take();
		let mut _localctx = RelOpContextExt::new(_parentctx.clone(), recog.base.get_state());
        recog.base.enter_rule(_localctx.clone(), 188, RULE_relOp);
        let mut _localctx: Rc<RelOpContextAll> = _localctx;
		let mut _la: isize = -1;
		let result: Result<(), ANTLRError> = (|| {

			recog.base.set_state(1286);
			recog.err_handler.sync(&mut recog.base)?;
			match recog.base.input.la(1) {
			 L_ANGLE_EQ 
				=> {
					let tmp = BinOpLessEqualsContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 1);
					_localctx = tmp;
					{
					recog.base.set_state(1276);
					recog.base.match_token(L_ANGLE_EQ,&mut recog.err_handler)?;

					}
				}

			 R_ANGLE_EQ 
				=> {
					let tmp = BinOpGreaterEqualsContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 2);
					_localctx = tmp;
					{
					recog.base.set_state(1277);
					recog.base.match_token(R_ANGLE_EQ,&mut recog.err_handler)?;

					}
				}

			 L_ANGLE 
				=> {
					let tmp = BinOpLessContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 3);
					_localctx = tmp;
					{
					recog.base.set_state(1278);
					recog.base.match_token(L_ANGLE,&mut recog.err_handler)?;

					}
				}

			 R_ANGLE 
				=> {
					let tmp = BinOpGreaterContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 4);
					_localctx = tmp;
					{
					recog.base.set_state(1279);
					recog.base.match_token(R_ANGLE,&mut recog.err_handler)?;

					}
				}

			 EQ_EQ 
				=> {
					let tmp = BinOpEqualsContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 5);
					_localctx = tmp;
					{
					recog.base.set_state(1280);
					recog.base.match_token(EQ_EQ,&mut recog.err_handler)?;

					}
				}

			 BANG_EQ 
				=> {
					let tmp = BinOpNotEqualsContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 6);
					_localctx = tmp;
					{
					recog.base.set_state(1281);
					recog.base.match_token(BANG_EQ,&mut recog.err_handler)?;

					}
				}

			 BANG | IN 
				=> {
					let tmp = BinOpInContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 7);
					_localctx = tmp;
					{
					recog.base.set_state(1283);
					recog.err_handler.sync(&mut recog.base)?;
					_la = recog.base.input.la(1);
					if _la==BANG {
						{
						recog.base.set_state(1282);
						let tmp = recog.base.match_token(BANG,&mut recog.err_handler)?;
						if let RelOpContextAll::BinOpInContext(ctx) = cast_mut::<_,RelOpContextAll >(&mut _localctx){
						ctx.not = Some(tmp.clone()); } else {unreachable!("cant cast");}  

						}
					}

					recog.base.set_state(1285);
					recog.base.match_token(IN,&mut recog.err_handler)?;

					}
				}

				_ => Err(ANTLRError::NoAltError(NoViableAltError::new(&mut recog.base)))?
			}
			Ok(())
		})();
		match result {
		Ok(_)=>{},
        Err(e @ ANTLRError::FallThrough(_)) => return Err(e),
		Err(ref re) => {
				//_localctx.exception = re;
				recog.err_handler.report_error(&mut recog.base, re);
				recog.err_handler.recover(&mut recog.base, re)?;
			}
		}
		recog.base.exit_rule();

		Ok(_localctx)
	}
}
//------------------- primitiveLit ----------------
#[derive(Debug)]
pub enum PrimitiveLitContextAll<'input>{
	PrimitiveLitCharContext(PrimitiveLitCharContext<'input>),
	PrimitiveLitTrueContext(PrimitiveLitTrueContext<'input>),
	PrimitiveLitIntContext(PrimitiveLitIntContext<'input>),
	PrimitiveLitFloatContext(PrimitiveLitFloatContext<'input>),
	PrimitiveLitStringLitContext(PrimitiveLitStringLitContext<'input>),
	PrimitiveLitFalseContext(PrimitiveLitFalseContext<'input>),
	PrimitiveLitNullContext(PrimitiveLitNullContext<'input>),
Error(PrimitiveLitContext<'input>)
}
antlr_rust::tid!{PrimitiveLitContextAll<'a>}

impl<'input> antlr_rust::parser_rule_context::DerefSeal for PrimitiveLitContextAll<'input>{}

impl<'input> LibSLParserContext<'input> for PrimitiveLitContextAll<'input>{}

impl<'input> Deref for PrimitiveLitContextAll<'input>{
	type Target = dyn PrimitiveLitContextAttrs<'input> + 'input;
	fn deref(&self) -> &Self::Target{
		use PrimitiveLitContextAll::*;
		match self{
			PrimitiveLitCharContext(inner) => inner,
			PrimitiveLitTrueContext(inner) => inner,
			PrimitiveLitIntContext(inner) => inner,
			PrimitiveLitFloatContext(inner) => inner,
			PrimitiveLitStringLitContext(inner) => inner,
			PrimitiveLitFalseContext(inner) => inner,
			PrimitiveLitNullContext(inner) => inner,
Error(inner) => inner
		}
	}
}
impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for PrimitiveLitContextAll<'input>{
    fn enter(&self, listener: &mut (dyn LibSLParserListener<'input> + 'a)) { self.deref().enter(listener) }
    fn exit(&self, listener: &mut (dyn LibSLParserListener<'input> + 'a)) { self.deref().exit(listener) }
}



pub type PrimitiveLitContext<'input> = BaseParserRuleContext<'input,PrimitiveLitContextExt<'input>>;

#[derive(Clone)]
pub struct PrimitiveLitContextExt<'input>{
ph:PhantomData<&'input str>
}

impl<'input> LibSLParserContext<'input> for PrimitiveLitContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for PrimitiveLitContext<'input>{
}

impl<'input> CustomRuleContext<'input> for PrimitiveLitContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_primitiveLit }
	//fn type_rule_index() -> usize where Self: Sized { RULE_primitiveLit }
}
antlr_rust::tid!{PrimitiveLitContextExt<'a>}

impl<'input> PrimitiveLitContextExt<'input>{
	fn new(parent: Option<Rc<dyn LibSLParserContext<'input> + 'input > >, invoking_state: isize) -> Rc<PrimitiveLitContextAll<'input>> {
		Rc::new(
		PrimitiveLitContextAll::Error(
			BaseParserRuleContext::new_parser_ctx(parent, invoking_state,PrimitiveLitContextExt{
				ph:PhantomData
			}),
		)
		)
	}
}

pub trait PrimitiveLitContextAttrs<'input>: LibSLParserContext<'input> + BorrowMut<PrimitiveLitContextExt<'input>>{


}

impl<'input> PrimitiveLitContextAttrs<'input> for PrimitiveLitContext<'input>{}

pub type PrimitiveLitCharContext<'input> = BaseParserRuleContext<'input,PrimitiveLitCharContextExt<'input>>;

pub trait PrimitiveLitCharContextAttrs<'input>: LibSLParserContext<'input>{
	/// Retrieves first TerminalNode corresponding to token CharacterLit
	/// Returns `None` if there is no child corresponding to token CharacterLit
	fn CharacterLit(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(CharacterLit, 0)
	}
}

impl<'input> PrimitiveLitCharContextAttrs<'input> for PrimitiveLitCharContext<'input>{}

pub struct PrimitiveLitCharContextExt<'input>{
	__base:PrimitiveLitContextExt<'input>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{PrimitiveLitCharContextExt<'a>}

impl<'input> LibSLParserContext<'input> for PrimitiveLitCharContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for PrimitiveLitCharContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_PrimitiveLitChar(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_PrimitiveLitChar(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for PrimitiveLitCharContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_primitiveLit }
	//fn type_rule_index() -> usize where Self: Sized { RULE_primitiveLit }
}

impl<'input> Borrow<PrimitiveLitContextExt<'input>> for PrimitiveLitCharContext<'input>{
	fn borrow(&self) -> &PrimitiveLitContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<PrimitiveLitContextExt<'input>> for PrimitiveLitCharContext<'input>{
	fn borrow_mut(&mut self) -> &mut PrimitiveLitContextExt<'input> { &mut self.__base }
}

impl<'input> PrimitiveLitContextAttrs<'input> for PrimitiveLitCharContext<'input> {}

impl<'input> PrimitiveLitCharContextExt<'input>{
	fn new(ctx: &dyn PrimitiveLitContextAttrs<'input>) -> Rc<PrimitiveLitContextAll<'input>>  {
		Rc::new(
			PrimitiveLitContextAll::PrimitiveLitCharContext(
				BaseParserRuleContext::copy_from(ctx,PrimitiveLitCharContextExt{
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type PrimitiveLitTrueContext<'input> = BaseParserRuleContext<'input,PrimitiveLitTrueContextExt<'input>>;

pub trait PrimitiveLitTrueContextAttrs<'input>: LibSLParserContext<'input>{
	/// Retrieves first TerminalNode corresponding to token TRUE
	/// Returns `None` if there is no child corresponding to token TRUE
	fn TRUE(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(TRUE, 0)
	}
}

impl<'input> PrimitiveLitTrueContextAttrs<'input> for PrimitiveLitTrueContext<'input>{}

pub struct PrimitiveLitTrueContextExt<'input>{
	__base:PrimitiveLitContextExt<'input>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{PrimitiveLitTrueContextExt<'a>}

impl<'input> LibSLParserContext<'input> for PrimitiveLitTrueContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for PrimitiveLitTrueContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_PrimitiveLitTrue(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_PrimitiveLitTrue(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for PrimitiveLitTrueContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_primitiveLit }
	//fn type_rule_index() -> usize where Self: Sized { RULE_primitiveLit }
}

impl<'input> Borrow<PrimitiveLitContextExt<'input>> for PrimitiveLitTrueContext<'input>{
	fn borrow(&self) -> &PrimitiveLitContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<PrimitiveLitContextExt<'input>> for PrimitiveLitTrueContext<'input>{
	fn borrow_mut(&mut self) -> &mut PrimitiveLitContextExt<'input> { &mut self.__base }
}

impl<'input> PrimitiveLitContextAttrs<'input> for PrimitiveLitTrueContext<'input> {}

impl<'input> PrimitiveLitTrueContextExt<'input>{
	fn new(ctx: &dyn PrimitiveLitContextAttrs<'input>) -> Rc<PrimitiveLitContextAll<'input>>  {
		Rc::new(
			PrimitiveLitContextAll::PrimitiveLitTrueContext(
				BaseParserRuleContext::copy_from(ctx,PrimitiveLitTrueContextExt{
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type PrimitiveLitIntContext<'input> = BaseParserRuleContext<'input,PrimitiveLitIntContextExt<'input>>;

pub trait PrimitiveLitIntContextAttrs<'input>: LibSLParserContext<'input>{
	/// Retrieves first TerminalNode corresponding to token IntegerLit
	/// Returns `None` if there is no child corresponding to token IntegerLit
	fn IntegerLit(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(IntegerLit, 0)
	}
}

impl<'input> PrimitiveLitIntContextAttrs<'input> for PrimitiveLitIntContext<'input>{}

pub struct PrimitiveLitIntContextExt<'input>{
	__base:PrimitiveLitContextExt<'input>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{PrimitiveLitIntContextExt<'a>}

impl<'input> LibSLParserContext<'input> for PrimitiveLitIntContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for PrimitiveLitIntContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_PrimitiveLitInt(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_PrimitiveLitInt(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for PrimitiveLitIntContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_primitiveLit }
	//fn type_rule_index() -> usize where Self: Sized { RULE_primitiveLit }
}

impl<'input> Borrow<PrimitiveLitContextExt<'input>> for PrimitiveLitIntContext<'input>{
	fn borrow(&self) -> &PrimitiveLitContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<PrimitiveLitContextExt<'input>> for PrimitiveLitIntContext<'input>{
	fn borrow_mut(&mut self) -> &mut PrimitiveLitContextExt<'input> { &mut self.__base }
}

impl<'input> PrimitiveLitContextAttrs<'input> for PrimitiveLitIntContext<'input> {}

impl<'input> PrimitiveLitIntContextExt<'input>{
	fn new(ctx: &dyn PrimitiveLitContextAttrs<'input>) -> Rc<PrimitiveLitContextAll<'input>>  {
		Rc::new(
			PrimitiveLitContextAll::PrimitiveLitIntContext(
				BaseParserRuleContext::copy_from(ctx,PrimitiveLitIntContextExt{
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type PrimitiveLitFloatContext<'input> = BaseParserRuleContext<'input,PrimitiveLitFloatContextExt<'input>>;

pub trait PrimitiveLitFloatContextAttrs<'input>: LibSLParserContext<'input>{
	/// Retrieves first TerminalNode corresponding to token FloatLit
	/// Returns `None` if there is no child corresponding to token FloatLit
	fn FloatLit(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(FloatLit, 0)
	}
}

impl<'input> PrimitiveLitFloatContextAttrs<'input> for PrimitiveLitFloatContext<'input>{}

pub struct PrimitiveLitFloatContextExt<'input>{
	__base:PrimitiveLitContextExt<'input>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{PrimitiveLitFloatContextExt<'a>}

impl<'input> LibSLParserContext<'input> for PrimitiveLitFloatContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for PrimitiveLitFloatContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_PrimitiveLitFloat(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_PrimitiveLitFloat(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for PrimitiveLitFloatContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_primitiveLit }
	//fn type_rule_index() -> usize where Self: Sized { RULE_primitiveLit }
}

impl<'input> Borrow<PrimitiveLitContextExt<'input>> for PrimitiveLitFloatContext<'input>{
	fn borrow(&self) -> &PrimitiveLitContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<PrimitiveLitContextExt<'input>> for PrimitiveLitFloatContext<'input>{
	fn borrow_mut(&mut self) -> &mut PrimitiveLitContextExt<'input> { &mut self.__base }
}

impl<'input> PrimitiveLitContextAttrs<'input> for PrimitiveLitFloatContext<'input> {}

impl<'input> PrimitiveLitFloatContextExt<'input>{
	fn new(ctx: &dyn PrimitiveLitContextAttrs<'input>) -> Rc<PrimitiveLitContextAll<'input>>  {
		Rc::new(
			PrimitiveLitContextAll::PrimitiveLitFloatContext(
				BaseParserRuleContext::copy_from(ctx,PrimitiveLitFloatContextExt{
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type PrimitiveLitStringLitContext<'input> = BaseParserRuleContext<'input,PrimitiveLitStringLitContextExt<'input>>;

pub trait PrimitiveLitStringLitContextAttrs<'input>: LibSLParserContext<'input>{
	/// Retrieves first TerminalNode corresponding to token StringLit
	/// Returns `None` if there is no child corresponding to token StringLit
	fn StringLit(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(StringLit, 0)
	}
}

impl<'input> PrimitiveLitStringLitContextAttrs<'input> for PrimitiveLitStringLitContext<'input>{}

pub struct PrimitiveLitStringLitContextExt<'input>{
	__base:PrimitiveLitContextExt<'input>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{PrimitiveLitStringLitContextExt<'a>}

impl<'input> LibSLParserContext<'input> for PrimitiveLitStringLitContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for PrimitiveLitStringLitContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_PrimitiveLitStringLit(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_PrimitiveLitStringLit(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for PrimitiveLitStringLitContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_primitiveLit }
	//fn type_rule_index() -> usize where Self: Sized { RULE_primitiveLit }
}

impl<'input> Borrow<PrimitiveLitContextExt<'input>> for PrimitiveLitStringLitContext<'input>{
	fn borrow(&self) -> &PrimitiveLitContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<PrimitiveLitContextExt<'input>> for PrimitiveLitStringLitContext<'input>{
	fn borrow_mut(&mut self) -> &mut PrimitiveLitContextExt<'input> { &mut self.__base }
}

impl<'input> PrimitiveLitContextAttrs<'input> for PrimitiveLitStringLitContext<'input> {}

impl<'input> PrimitiveLitStringLitContextExt<'input>{
	fn new(ctx: &dyn PrimitiveLitContextAttrs<'input>) -> Rc<PrimitiveLitContextAll<'input>>  {
		Rc::new(
			PrimitiveLitContextAll::PrimitiveLitStringLitContext(
				BaseParserRuleContext::copy_from(ctx,PrimitiveLitStringLitContextExt{
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type PrimitiveLitFalseContext<'input> = BaseParserRuleContext<'input,PrimitiveLitFalseContextExt<'input>>;

pub trait PrimitiveLitFalseContextAttrs<'input>: LibSLParserContext<'input>{
	/// Retrieves first TerminalNode corresponding to token FALSE
	/// Returns `None` if there is no child corresponding to token FALSE
	fn FALSE(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(FALSE, 0)
	}
}

impl<'input> PrimitiveLitFalseContextAttrs<'input> for PrimitiveLitFalseContext<'input>{}

pub struct PrimitiveLitFalseContextExt<'input>{
	__base:PrimitiveLitContextExt<'input>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{PrimitiveLitFalseContextExt<'a>}

impl<'input> LibSLParserContext<'input> for PrimitiveLitFalseContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for PrimitiveLitFalseContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_PrimitiveLitFalse(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_PrimitiveLitFalse(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for PrimitiveLitFalseContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_primitiveLit }
	//fn type_rule_index() -> usize where Self: Sized { RULE_primitiveLit }
}

impl<'input> Borrow<PrimitiveLitContextExt<'input>> for PrimitiveLitFalseContext<'input>{
	fn borrow(&self) -> &PrimitiveLitContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<PrimitiveLitContextExt<'input>> for PrimitiveLitFalseContext<'input>{
	fn borrow_mut(&mut self) -> &mut PrimitiveLitContextExt<'input> { &mut self.__base }
}

impl<'input> PrimitiveLitContextAttrs<'input> for PrimitiveLitFalseContext<'input> {}

impl<'input> PrimitiveLitFalseContextExt<'input>{
	fn new(ctx: &dyn PrimitiveLitContextAttrs<'input>) -> Rc<PrimitiveLitContextAll<'input>>  {
		Rc::new(
			PrimitiveLitContextAll::PrimitiveLitFalseContext(
				BaseParserRuleContext::copy_from(ctx,PrimitiveLitFalseContextExt{
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type PrimitiveLitNullContext<'input> = BaseParserRuleContext<'input,PrimitiveLitNullContextExt<'input>>;

pub trait PrimitiveLitNullContextAttrs<'input>: LibSLParserContext<'input>{
	/// Retrieves first TerminalNode corresponding to token NULL
	/// Returns `None` if there is no child corresponding to token NULL
	fn NULL(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(NULL, 0)
	}
}

impl<'input> PrimitiveLitNullContextAttrs<'input> for PrimitiveLitNullContext<'input>{}

pub struct PrimitiveLitNullContextExt<'input>{
	__base:PrimitiveLitContextExt<'input>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{PrimitiveLitNullContextExt<'a>}

impl<'input> LibSLParserContext<'input> for PrimitiveLitNullContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for PrimitiveLitNullContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_PrimitiveLitNull(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_PrimitiveLitNull(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for PrimitiveLitNullContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_primitiveLit }
	//fn type_rule_index() -> usize where Self: Sized { RULE_primitiveLit }
}

impl<'input> Borrow<PrimitiveLitContextExt<'input>> for PrimitiveLitNullContext<'input>{
	fn borrow(&self) -> &PrimitiveLitContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<PrimitiveLitContextExt<'input>> for PrimitiveLitNullContext<'input>{
	fn borrow_mut(&mut self) -> &mut PrimitiveLitContextExt<'input> { &mut self.__base }
}

impl<'input> PrimitiveLitContextAttrs<'input> for PrimitiveLitNullContext<'input> {}

impl<'input> PrimitiveLitNullContextExt<'input>{
	fn new(ctx: &dyn PrimitiveLitContextAttrs<'input>) -> Rc<PrimitiveLitContextAll<'input>>  {
		Rc::new(
			PrimitiveLitContextAll::PrimitiveLitNullContext(
				BaseParserRuleContext::copy_from(ctx,PrimitiveLitNullContextExt{
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

impl<'input, I, H> LibSLParser<'input, I, H>
where
    I: TokenStream<'input, TF = LocalTokenFactory<'input> > + TidAble<'input>,
    H: ErrorStrategy<'input,BaseParserType<'input,I>>
{
	pub fn primitiveLit(&mut self,)
	-> Result<Rc<PrimitiveLitContextAll<'input>>,ANTLRError> {
		let mut recog = self;
		let _parentctx = recog.ctx.take();
		let mut _localctx = PrimitiveLitContextExt::new(_parentctx.clone(), recog.base.get_state());
        recog.base.enter_rule(_localctx.clone(), 190, RULE_primitiveLit);
        let mut _localctx: Rc<PrimitiveLitContextAll> = _localctx;
		let result: Result<(), ANTLRError> = (|| {

			recog.base.set_state(1295);
			recog.err_handler.sync(&mut recog.base)?;
			match recog.base.input.la(1) {
			 IntegerLit 
				=> {
					let tmp = PrimitiveLitIntContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 1);
					_localctx = tmp;
					{
					recog.base.set_state(1288);
					recog.base.match_token(IntegerLit,&mut recog.err_handler)?;

					}
				}

			 FloatLit 
				=> {
					let tmp = PrimitiveLitFloatContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 2);
					_localctx = tmp;
					{
					recog.base.set_state(1289);
					recog.base.match_token(FloatLit,&mut recog.err_handler)?;

					}
				}

			 StringLit 
				=> {
					let tmp = PrimitiveLitStringLitContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 3);
					_localctx = tmp;
					{
					recog.base.set_state(1290);
					recog.base.match_token(StringLit,&mut recog.err_handler)?;

					}
				}

			 CharacterLit 
				=> {
					let tmp = PrimitiveLitCharContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 4);
					_localctx = tmp;
					{
					recog.base.set_state(1291);
					recog.base.match_token(CharacterLit,&mut recog.err_handler)?;

					}
				}

			 TRUE 
				=> {
					let tmp = PrimitiveLitTrueContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 5);
					_localctx = tmp;
					{
					recog.base.set_state(1292);
					recog.base.match_token(TRUE,&mut recog.err_handler)?;

					}
				}

			 FALSE 
				=> {
					let tmp = PrimitiveLitFalseContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 6);
					_localctx = tmp;
					{
					recog.base.set_state(1293);
					recog.base.match_token(FALSE,&mut recog.err_handler)?;

					}
				}

			 NULL 
				=> {
					let tmp = PrimitiveLitNullContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 7);
					_localctx = tmp;
					{
					recog.base.set_state(1294);
					recog.base.match_token(NULL,&mut recog.err_handler)?;

					}
				}

				_ => Err(ANTLRError::NoAltError(NoViableAltError::new(&mut recog.base)))?
			}
			Ok(())
		})();
		match result {
		Ok(_)=>{},
        Err(e @ ANTLRError::FallThrough(_)) => return Err(e),
		Err(ref re) => {
				//_localctx.exception = re;
				recog.err_handler.report_error(&mut recog.base, re);
				recog.err_handler.recover(&mut recog.base, re)?;
			}
		}
		recog.base.exit_rule();

		Ok(_localctx)
	}
}
//------------------- arrayLitExpr ----------------
pub type ArrayLitExprContextAll<'input> = ArrayLitExprContext<'input>;


pub type ArrayLitExprContext<'input> = BaseParserRuleContext<'input,ArrayLitExprContextExt<'input>>;

#[derive(Clone)]
pub struct ArrayLitExprContextExt<'input>{
	pub elems: Option<Rc<ExprListContextAll<'input>>>,
ph:PhantomData<&'input str>
}

impl<'input> LibSLParserContext<'input> for ArrayLitExprContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for ArrayLitExprContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_arrayLitExpr(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_arrayLitExpr(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for ArrayLitExprContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_arrayLitExpr }
	//fn type_rule_index() -> usize where Self: Sized { RULE_arrayLitExpr }
}
antlr_rust::tid!{ArrayLitExprContextExt<'a>}

impl<'input> ArrayLitExprContextExt<'input>{
	fn new(parent: Option<Rc<dyn LibSLParserContext<'input> + 'input > >, invoking_state: isize) -> Rc<ArrayLitExprContextAll<'input>> {
		Rc::new(
			BaseParserRuleContext::new_parser_ctx(parent, invoking_state,ArrayLitExprContextExt{
				elems: None, 
				ph:PhantomData
			}),
		)
	}
}

pub trait ArrayLitExprContextAttrs<'input>: LibSLParserContext<'input> + BorrowMut<ArrayLitExprContextExt<'input>>{

/// Retrieves first TerminalNode corresponding to token L_BRACKET
/// Returns `None` if there is no child corresponding to token L_BRACKET
fn L_BRACKET(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(L_BRACKET, 0)
}
/// Retrieves first TerminalNode corresponding to token R_BRACKET
/// Returns `None` if there is no child corresponding to token R_BRACKET
fn R_BRACKET(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(R_BRACKET, 0)
}
fn exprList(&self) -> Option<Rc<ExprListContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}
/// Retrieves first TerminalNode corresponding to token COMMA
/// Returns `None` if there is no child corresponding to token COMMA
fn COMMA(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(COMMA, 0)
}

}

impl<'input> ArrayLitExprContextAttrs<'input> for ArrayLitExprContext<'input>{}

impl<'input, I, H> LibSLParser<'input, I, H>
where
    I: TokenStream<'input, TF = LocalTokenFactory<'input> > + TidAble<'input>,
    H: ErrorStrategy<'input,BaseParserType<'input,I>>
{
	pub fn arrayLitExpr(&mut self,)
	-> Result<Rc<ArrayLitExprContextAll<'input>>,ANTLRError> {
		let mut recog = self;
		let _parentctx = recog.ctx.take();
		let mut _localctx = ArrayLitExprContextExt::new(_parentctx.clone(), recog.base.get_state());
        recog.base.enter_rule(_localctx.clone(), 192, RULE_arrayLitExpr);
        let mut _localctx: Rc<ArrayLitExprContextAll> = _localctx;
		let mut _la: isize = -1;
		let result: Result<(), ANTLRError> = (|| {

			//recog.base.enter_outer_alt(_localctx.clone(), 1);
			recog.base.enter_outer_alt(None, 1);
			{
			recog.base.set_state(1297);
			recog.base.match_token(L_BRACKET,&mut recog.err_handler)?;

			recog.base.set_state(1302);
			recog.err_handler.sync(&mut recog.base)?;
			_la = recog.base.input.la(1);
			if (((_la) & !0x3f) == 0 && ((1usize << _la) & 68682064) != 0) || _la==TILDE || _la==NEW || ((((_la - 69)) & !0x3f) == 0 && ((1usize << (_la - 69)) & 512626737) != 0) {
				{
				/*InvokeRule exprList*/
				recog.base.set_state(1298);
				let tmp = recog.exprList()?;
				 cast_mut::<_,ArrayLitExprContext >(&mut _localctx).elems = Some(tmp.clone());
				  

				recog.base.set_state(1300);
				recog.err_handler.sync(&mut recog.base)?;
				_la = recog.base.input.la(1);
				if _la==COMMA {
					{
					recog.base.set_state(1299);
					recog.base.match_token(COMMA,&mut recog.err_handler)?;

					}
				}

				}
			}

			recog.base.set_state(1304);
			recog.base.match_token(R_BRACKET,&mut recog.err_handler)?;

			}
			Ok(())
		})();
		match result {
		Ok(_)=>{},
        Err(e @ ANTLRError::FallThrough(_)) => return Err(e),
		Err(ref re) => {
				//_localctx.exception = re;
				recog.err_handler.report_error(&mut recog.base, re);
				recog.err_handler.recover(&mut recog.base, re)?;
			}
		}
		recog.base.exit_rule();

		Ok(_localctx)
	}
}
//------------------- setLitExpr ----------------
pub type SetLitExprContextAll<'input> = SetLitExprContext<'input>;


pub type SetLitExprContext<'input> = BaseParserRuleContext<'input,SetLitExprContextExt<'input>>;

#[derive(Clone)]
pub struct SetLitExprContextExt<'input>{
	pub elems: Option<Rc<ExprListContextAll<'input>>>,
ph:PhantomData<&'input str>
}

impl<'input> LibSLParserContext<'input> for SetLitExprContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for SetLitExprContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_setLitExpr(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_setLitExpr(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for SetLitExprContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_setLitExpr }
	//fn type_rule_index() -> usize where Self: Sized { RULE_setLitExpr }
}
antlr_rust::tid!{SetLitExprContextExt<'a>}

impl<'input> SetLitExprContextExt<'input>{
	fn new(parent: Option<Rc<dyn LibSLParserContext<'input> + 'input > >, invoking_state: isize) -> Rc<SetLitExprContextAll<'input>> {
		Rc::new(
			BaseParserRuleContext::new_parser_ctx(parent, invoking_state,SetLitExprContextExt{
				elems: None, 
				ph:PhantomData
			}),
		)
	}
}

pub trait SetLitExprContextAttrs<'input>: LibSLParserContext<'input> + BorrowMut<SetLitExprContextExt<'input>>{

/// Retrieves first TerminalNode corresponding to token L_BRACE
/// Returns `None` if there is no child corresponding to token L_BRACE
fn L_BRACE(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(L_BRACE, 0)
}
/// Retrieves first TerminalNode corresponding to token R_BRACE
/// Returns `None` if there is no child corresponding to token R_BRACE
fn R_BRACE(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(R_BRACE, 0)
}
fn exprList(&self) -> Option<Rc<ExprListContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}
/// Retrieves first TerminalNode corresponding to token COMMA
/// Returns `None` if there is no child corresponding to token COMMA
fn COMMA(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(COMMA, 0)
}

}

impl<'input> SetLitExprContextAttrs<'input> for SetLitExprContext<'input>{}

impl<'input, I, H> LibSLParser<'input, I, H>
where
    I: TokenStream<'input, TF = LocalTokenFactory<'input> > + TidAble<'input>,
    H: ErrorStrategy<'input,BaseParserType<'input,I>>
{
	pub fn setLitExpr(&mut self,)
	-> Result<Rc<SetLitExprContextAll<'input>>,ANTLRError> {
		let mut recog = self;
		let _parentctx = recog.ctx.take();
		let mut _localctx = SetLitExprContextExt::new(_parentctx.clone(), recog.base.get_state());
        recog.base.enter_rule(_localctx.clone(), 194, RULE_setLitExpr);
        let mut _localctx: Rc<SetLitExprContextAll> = _localctx;
		let mut _la: isize = -1;
		let result: Result<(), ANTLRError> = (|| {

			//recog.base.enter_outer_alt(_localctx.clone(), 1);
			recog.base.enter_outer_alt(None, 1);
			{
			recog.base.set_state(1306);
			recog.base.match_token(L_BRACE,&mut recog.err_handler)?;

			recog.base.set_state(1311);
			recog.err_handler.sync(&mut recog.base)?;
			_la = recog.base.input.la(1);
			if (((_la) & !0x3f) == 0 && ((1usize << _la) & 68682064) != 0) || _la==TILDE || _la==NEW || ((((_la - 69)) & !0x3f) == 0 && ((1usize << (_la - 69)) & 512626737) != 0) {
				{
				/*InvokeRule exprList*/
				recog.base.set_state(1307);
				let tmp = recog.exprList()?;
				 cast_mut::<_,SetLitExprContext >(&mut _localctx).elems = Some(tmp.clone());
				  

				recog.base.set_state(1309);
				recog.err_handler.sync(&mut recog.base)?;
				_la = recog.base.input.la(1);
				if _la==COMMA {
					{
					recog.base.set_state(1308);
					recog.base.match_token(COMMA,&mut recog.err_handler)?;

					}
				}

				}
			}

			recog.base.set_state(1313);
			recog.base.match_token(R_BRACE,&mut recog.err_handler)?;

			}
			Ok(())
		})();
		match result {
		Ok(_)=>{},
        Err(e @ ANTLRError::FallThrough(_)) => return Err(e),
		Err(ref re) => {
				//_localctx.exception = re;
				recog.err_handler.report_error(&mut recog.base, re);
				recog.err_handler.recover(&mut recog.base, re)?;
			}
		}
		recog.base.exit_rule();

		Ok(_localctx)
	}
}
//------------------- actionCallExpr ----------------
pub type ActionCallExprContextAll<'input> = ActionCallExprContext<'input>;


pub type ActionCallExprContext<'input> = BaseParserRuleContext<'input,ActionCallExprContextExt<'input>>;

#[derive(Clone)]
pub struct ActionCallExprContextExt<'input>{
	pub name: Option<Rc<IdentContextAll<'input>>>,
	pub typeArgs: Option<Rc<TypeArgSpecContextAll<'input>>>,
	pub args: Option<Rc<ExprListContextAll<'input>>>,
ph:PhantomData<&'input str>
}

impl<'input> LibSLParserContext<'input> for ActionCallExprContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for ActionCallExprContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_actionCallExpr(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_actionCallExpr(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for ActionCallExprContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_actionCallExpr }
	//fn type_rule_index() -> usize where Self: Sized { RULE_actionCallExpr }
}
antlr_rust::tid!{ActionCallExprContextExt<'a>}

impl<'input> ActionCallExprContextExt<'input>{
	fn new(parent: Option<Rc<dyn LibSLParserContext<'input> + 'input > >, invoking_state: isize) -> Rc<ActionCallExprContextAll<'input>> {
		Rc::new(
			BaseParserRuleContext::new_parser_ctx(parent, invoking_state,ActionCallExprContextExt{
				name: None, typeArgs: None, args: None, 
				ph:PhantomData
			}),
		)
	}
}

pub trait ActionCallExprContextAttrs<'input>: LibSLParserContext<'input> + BorrowMut<ActionCallExprContextExt<'input>>{

/// Retrieves first TerminalNode corresponding to token ACTION
/// Returns `None` if there is no child corresponding to token ACTION
fn ACTION(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(ACTION, 0)
}
/// Retrieves first TerminalNode corresponding to token L_PAREN
/// Returns `None` if there is no child corresponding to token L_PAREN
fn L_PAREN(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(L_PAREN, 0)
}
/// Retrieves first TerminalNode corresponding to token R_PAREN
/// Returns `None` if there is no child corresponding to token R_PAREN
fn R_PAREN(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(R_PAREN, 0)
}
fn ident(&self) -> Option<Rc<IdentContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}
fn typeArgSpec(&self) -> Option<Rc<TypeArgSpecContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}
fn exprList(&self) -> Option<Rc<ExprListContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}
/// Retrieves first TerminalNode corresponding to token COMMA
/// Returns `None` if there is no child corresponding to token COMMA
fn COMMA(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(COMMA, 0)
}

}

impl<'input> ActionCallExprContextAttrs<'input> for ActionCallExprContext<'input>{}

impl<'input, I, H> LibSLParser<'input, I, H>
where
    I: TokenStream<'input, TF = LocalTokenFactory<'input> > + TidAble<'input>,
    H: ErrorStrategy<'input,BaseParserType<'input,I>>
{
	pub fn actionCallExpr(&mut self,)
	-> Result<Rc<ActionCallExprContextAll<'input>>,ANTLRError> {
		let mut recog = self;
		let _parentctx = recog.ctx.take();
		let mut _localctx = ActionCallExprContextExt::new(_parentctx.clone(), recog.base.get_state());
        recog.base.enter_rule(_localctx.clone(), 196, RULE_actionCallExpr);
        let mut _localctx: Rc<ActionCallExprContextAll> = _localctx;
		let mut _la: isize = -1;
		let result: Result<(), ANTLRError> = (|| {

			//recog.base.enter_outer_alt(_localctx.clone(), 1);
			recog.base.enter_outer_alt(None, 1);
			{
			recog.base.set_state(1315);
			recog.base.match_token(ACTION,&mut recog.err_handler)?;

			/*InvokeRule ident*/
			recog.base.set_state(1316);
			let tmp = recog.ident()?;
			 cast_mut::<_,ActionCallExprContext >(&mut _localctx).name = Some(tmp.clone());
			  

			recog.base.set_state(1318);
			recog.err_handler.sync(&mut recog.base)?;
			_la = recog.base.input.la(1);
			if _la==L_ANGLE {
				{
				/*InvokeRule typeArgSpec*/
				recog.base.set_state(1317);
				let tmp = recog.typeArgSpec()?;
				 cast_mut::<_,ActionCallExprContext >(&mut _localctx).typeArgs = Some(tmp.clone());
				  

				}
			}

			recog.base.set_state(1320);
			recog.base.match_token(L_PAREN,&mut recog.err_handler)?;

			recog.base.set_state(1325);
			recog.err_handler.sync(&mut recog.base)?;
			_la = recog.base.input.la(1);
			if (((_la) & !0x3f) == 0 && ((1usize << _la) & 68682064) != 0) || _la==TILDE || _la==NEW || ((((_la - 69)) & !0x3f) == 0 && ((1usize << (_la - 69)) & 512626737) != 0) {
				{
				/*InvokeRule exprList*/
				recog.base.set_state(1321);
				let tmp = recog.exprList()?;
				 cast_mut::<_,ActionCallExprContext >(&mut _localctx).args = Some(tmp.clone());
				  

				recog.base.set_state(1323);
				recog.err_handler.sync(&mut recog.base)?;
				_la = recog.base.input.la(1);
				if _la==COMMA {
					{
					recog.base.set_state(1322);
					recog.base.match_token(COMMA,&mut recog.err_handler)?;

					}
				}

				}
			}

			recog.base.set_state(1327);
			recog.base.match_token(R_PAREN,&mut recog.err_handler)?;

			}
			Ok(())
		})();
		match result {
		Ok(_)=>{},
        Err(e @ ANTLRError::FallThrough(_)) => return Err(e),
		Err(ref re) => {
				//_localctx.exception = re;
				recog.err_handler.report_error(&mut recog.base, re);
				recog.err_handler.recover(&mut recog.base, re)?;
			}
		}
		recog.base.exit_rule();

		Ok(_localctx)
	}
}
//------------------- instantiationExpr ----------------
pub type InstantiationExprContextAll<'input> = InstantiationExprContext<'input>;


pub type InstantiationExprContext<'input> = BaseParserRuleContext<'input,InstantiationExprContextExt<'input>>;

#[derive(Clone)]
pub struct InstantiationExprContextExt<'input>{
	pub name: Option<Rc<FullNameContextAll<'input>>>,
	pub typeArgs: Option<Rc<TypeArgSpecContextAll<'input>>>,
	pub args: Option<Rc<ConstructorArgListContextAll<'input>>>,
ph:PhantomData<&'input str>
}

impl<'input> LibSLParserContext<'input> for InstantiationExprContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for InstantiationExprContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_instantiationExpr(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_instantiationExpr(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for InstantiationExprContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_instantiationExpr }
	//fn type_rule_index() -> usize where Self: Sized { RULE_instantiationExpr }
}
antlr_rust::tid!{InstantiationExprContextExt<'a>}

impl<'input> InstantiationExprContextExt<'input>{
	fn new(parent: Option<Rc<dyn LibSLParserContext<'input> + 'input > >, invoking_state: isize) -> Rc<InstantiationExprContextAll<'input>> {
		Rc::new(
			BaseParserRuleContext::new_parser_ctx(parent, invoking_state,InstantiationExprContextExt{
				name: None, typeArgs: None, args: None, 
				ph:PhantomData
			}),
		)
	}
}

pub trait InstantiationExprContextAttrs<'input>: LibSLParserContext<'input> + BorrowMut<InstantiationExprContextExt<'input>>{

/// Retrieves first TerminalNode corresponding to token NEW
/// Returns `None` if there is no child corresponding to token NEW
fn NEW(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(NEW, 0)
}
/// Retrieves first TerminalNode corresponding to token L_PAREN
/// Returns `None` if there is no child corresponding to token L_PAREN
fn L_PAREN(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(L_PAREN, 0)
}
/// Retrieves first TerminalNode corresponding to token R_PAREN
/// Returns `None` if there is no child corresponding to token R_PAREN
fn R_PAREN(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(R_PAREN, 0)
}
fn fullName(&self) -> Option<Rc<FullNameContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}
fn typeArgSpec(&self) -> Option<Rc<TypeArgSpecContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}
fn constructorArgList(&self) -> Option<Rc<ConstructorArgListContextAll<'input>>> where Self:Sized{
	self.child_of_type(0)
}
/// Retrieves first TerminalNode corresponding to token COMMA
/// Returns `None` if there is no child corresponding to token COMMA
fn COMMA(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(COMMA, 0)
}

}

impl<'input> InstantiationExprContextAttrs<'input> for InstantiationExprContext<'input>{}

impl<'input, I, H> LibSLParser<'input, I, H>
where
    I: TokenStream<'input, TF = LocalTokenFactory<'input> > + TidAble<'input>,
    H: ErrorStrategy<'input,BaseParserType<'input,I>>
{
	pub fn instantiationExpr(&mut self,)
	-> Result<Rc<InstantiationExprContextAll<'input>>,ANTLRError> {
		let mut recog = self;
		let _parentctx = recog.ctx.take();
		let mut _localctx = InstantiationExprContextExt::new(_parentctx.clone(), recog.base.get_state());
        recog.base.enter_rule(_localctx.clone(), 198, RULE_instantiationExpr);
        let mut _localctx: Rc<InstantiationExprContextAll> = _localctx;
		let mut _la: isize = -1;
		let result: Result<(), ANTLRError> = (|| {

			//recog.base.enter_outer_alt(_localctx.clone(), 1);
			recog.base.enter_outer_alt(None, 1);
			{
			recog.base.set_state(1329);
			recog.base.match_token(NEW,&mut recog.err_handler)?;

			/*InvokeRule fullName*/
			recog.base.set_state(1330);
			let tmp = recog.fullName()?;
			 cast_mut::<_,InstantiationExprContext >(&mut _localctx).name = Some(tmp.clone());
			  

			recog.base.set_state(1332);
			recog.err_handler.sync(&mut recog.base)?;
			_la = recog.base.input.la(1);
			if _la==L_ANGLE {
				{
				/*InvokeRule typeArgSpec*/
				recog.base.set_state(1331);
				let tmp = recog.typeArgSpec()?;
				 cast_mut::<_,InstantiationExprContext >(&mut _localctx).typeArgs = Some(tmp.clone());
				  

				}
			}

			recog.base.set_state(1334);
			recog.base.match_token(L_PAREN,&mut recog.err_handler)?;

			recog.base.set_state(1339);
			recog.err_handler.sync(&mut recog.base)?;
			_la = recog.base.input.la(1);
			if ((((_la - 60)) & !0x3f) == 0 && ((1usize << (_la - 60)) & 469762049) != 0) || _la==Identifier {
				{
				/*InvokeRule constructorArgList*/
				recog.base.set_state(1335);
				let tmp = recog.constructorArgList()?;
				 cast_mut::<_,InstantiationExprContext >(&mut _localctx).args = Some(tmp.clone());
				  

				recog.base.set_state(1337);
				recog.err_handler.sync(&mut recog.base)?;
				_la = recog.base.input.la(1);
				if _la==COMMA {
					{
					recog.base.set_state(1336);
					recog.base.match_token(COMMA,&mut recog.err_handler)?;

					}
				}

				}
			}

			recog.base.set_state(1341);
			recog.base.match_token(R_PAREN,&mut recog.err_handler)?;

			}
			Ok(())
		})();
		match result {
		Ok(_)=>{},
        Err(e @ ANTLRError::FallThrough(_)) => return Err(e),
		Err(ref re) => {
				//_localctx.exception = re;
				recog.err_handler.report_error(&mut recog.base, re);
				recog.err_handler.recover(&mut recog.base, re)?;
			}
		}
		recog.base.exit_rule();

		Ok(_localctx)
	}
}
//------------------- constructorArgList ----------------
pub type ConstructorArgListContextAll<'input> = ConstructorArgListContext<'input>;


pub type ConstructorArgListContext<'input> = BaseParserRuleContext<'input,ConstructorArgListContextExt<'input>>;

#[derive(Clone)]
pub struct ConstructorArgListContextExt<'input>{
	pub constructorArg: Option<Rc<ConstructorArgContextAll<'input>>>,
	pub args:Vec<Rc<ConstructorArgContextAll<'input>>>,
ph:PhantomData<&'input str>
}

impl<'input> LibSLParserContext<'input> for ConstructorArgListContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for ConstructorArgListContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_constructorArgList(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_constructorArgList(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for ConstructorArgListContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_constructorArgList }
	//fn type_rule_index() -> usize where Self: Sized { RULE_constructorArgList }
}
antlr_rust::tid!{ConstructorArgListContextExt<'a>}

impl<'input> ConstructorArgListContextExt<'input>{
	fn new(parent: Option<Rc<dyn LibSLParserContext<'input> + 'input > >, invoking_state: isize) -> Rc<ConstructorArgListContextAll<'input>> {
		Rc::new(
			BaseParserRuleContext::new_parser_ctx(parent, invoking_state,ConstructorArgListContextExt{
				constructorArg: None, 
				args: Vec::new(), 
				ph:PhantomData
			}),
		)
	}
}

pub trait ConstructorArgListContextAttrs<'input>: LibSLParserContext<'input> + BorrowMut<ConstructorArgListContextExt<'input>>{

fn constructorArg_all(&self) ->  Vec<Rc<ConstructorArgContextAll<'input>>> where Self:Sized{
	self.children_of_type()
}
fn constructorArg(&self, i: usize) -> Option<Rc<ConstructorArgContextAll<'input>>> where Self:Sized{
	self.child_of_type(i)
}
/// Retrieves all `TerminalNode`s corresponding to token COMMA in current rule
fn COMMA_all(&self) -> Vec<Rc<TerminalNode<'input,LibSLParserContextType>>>  where Self:Sized{
	self.get_tokens(COMMA)
}
/// Retrieves 'i's TerminalNode corresponding to token COMMA, starting from 0.
/// Returns `None` if number of children corresponding to token COMMA is less or equal than `i`.
fn COMMA(&self, i: usize) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(COMMA, i)
}

}

impl<'input> ConstructorArgListContextAttrs<'input> for ConstructorArgListContext<'input>{}

impl<'input, I, H> LibSLParser<'input, I, H>
where
    I: TokenStream<'input, TF = LocalTokenFactory<'input> > + TidAble<'input>,
    H: ErrorStrategy<'input,BaseParserType<'input,I>>
{
	pub fn constructorArgList(&mut self,)
	-> Result<Rc<ConstructorArgListContextAll<'input>>,ANTLRError> {
		let mut recog = self;
		let _parentctx = recog.ctx.take();
		let mut _localctx = ConstructorArgListContextExt::new(_parentctx.clone(), recog.base.get_state());
        recog.base.enter_rule(_localctx.clone(), 200, RULE_constructorArgList);
        let mut _localctx: Rc<ConstructorArgListContextAll> = _localctx;
		let result: Result<(), ANTLRError> = (|| {

			let mut _alt: isize;
			//recog.base.enter_outer_alt(_localctx.clone(), 1);
			recog.base.enter_outer_alt(None, 1);
			{
			/*InvokeRule constructorArg*/
			recog.base.set_state(1343);
			let tmp = recog.constructorArg()?;
			 cast_mut::<_,ConstructorArgListContext >(&mut _localctx).constructorArg = Some(tmp.clone());
			  

			let temp =  cast_mut::<_,ConstructorArgListContext >(&mut _localctx).constructorArg.clone().unwrap()
			 ;
			 cast_mut::<_,ConstructorArgListContext >(&mut _localctx).args.push(temp);
			  
			recog.base.set_state(1348);
			recog.err_handler.sync(&mut recog.base)?;
			_alt = recog.interpreter.adaptive_predict(177,&mut recog.base)?;
			while { _alt!=2 && _alt!=INVALID_ALT } {
				if _alt==1 {
					{
					{
					recog.base.set_state(1344);
					recog.base.match_token(COMMA,&mut recog.err_handler)?;

					/*InvokeRule constructorArg*/
					recog.base.set_state(1345);
					let tmp = recog.constructorArg()?;
					 cast_mut::<_,ConstructorArgListContext >(&mut _localctx).constructorArg = Some(tmp.clone());
					  

					let temp =  cast_mut::<_,ConstructorArgListContext >(&mut _localctx).constructorArg.clone().unwrap()
					 ;
					 cast_mut::<_,ConstructorArgListContext >(&mut _localctx).args.push(temp);
					  
					}
					} 
				}
				recog.base.set_state(1350);
				recog.err_handler.sync(&mut recog.base)?;
				_alt = recog.interpreter.adaptive_predict(177,&mut recog.base)?;
			}
			}
			Ok(())
		})();
		match result {
		Ok(_)=>{},
        Err(e @ ANTLRError::FallThrough(_)) => return Err(e),
		Err(ref re) => {
				//_localctx.exception = re;
				recog.err_handler.report_error(&mut recog.base, re);
				recog.err_handler.recover(&mut recog.base, re)?;
			}
		}
		recog.base.exit_rule();

		Ok(_localctx)
	}
}
//------------------- constructorArg ----------------
#[derive(Debug)]
pub enum ConstructorArgContextAll<'input>{
	ConstructorArgStateContext(ConstructorArgStateContext<'input>),
	ConstructorArgVarContext(ConstructorArgVarContext<'input>),
Error(ConstructorArgContext<'input>)
}
antlr_rust::tid!{ConstructorArgContextAll<'a>}

impl<'input> antlr_rust::parser_rule_context::DerefSeal for ConstructorArgContextAll<'input>{}

impl<'input> LibSLParserContext<'input> for ConstructorArgContextAll<'input>{}

impl<'input> Deref for ConstructorArgContextAll<'input>{
	type Target = dyn ConstructorArgContextAttrs<'input> + 'input;
	fn deref(&self) -> &Self::Target{
		use ConstructorArgContextAll::*;
		match self{
			ConstructorArgStateContext(inner) => inner,
			ConstructorArgVarContext(inner) => inner,
Error(inner) => inner
		}
	}
}
impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for ConstructorArgContextAll<'input>{
    fn enter(&self, listener: &mut (dyn LibSLParserListener<'input> + 'a)) { self.deref().enter(listener) }
    fn exit(&self, listener: &mut (dyn LibSLParserListener<'input> + 'a)) { self.deref().exit(listener) }
}



pub type ConstructorArgContext<'input> = BaseParserRuleContext<'input,ConstructorArgContextExt<'input>>;

#[derive(Clone)]
pub struct ConstructorArgContextExt<'input>{
ph:PhantomData<&'input str>
}

impl<'input> LibSLParserContext<'input> for ConstructorArgContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for ConstructorArgContext<'input>{
}

impl<'input> CustomRuleContext<'input> for ConstructorArgContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_constructorArg }
	//fn type_rule_index() -> usize where Self: Sized { RULE_constructorArg }
}
antlr_rust::tid!{ConstructorArgContextExt<'a>}

impl<'input> ConstructorArgContextExt<'input>{
	fn new(parent: Option<Rc<dyn LibSLParserContext<'input> + 'input > >, invoking_state: isize) -> Rc<ConstructorArgContextAll<'input>> {
		Rc::new(
		ConstructorArgContextAll::Error(
			BaseParserRuleContext::new_parser_ctx(parent, invoking_state,ConstructorArgContextExt{
				ph:PhantomData
			}),
		)
		)
	}
}

pub trait ConstructorArgContextAttrs<'input>: LibSLParserContext<'input> + BorrowMut<ConstructorArgContextExt<'input>>{


}

impl<'input> ConstructorArgContextAttrs<'input> for ConstructorArgContext<'input>{}

pub type ConstructorArgStateContext<'input> = BaseParserRuleContext<'input,ConstructorArgStateContextExt<'input>>;

pub trait ConstructorArgStateContextAttrs<'input>: LibSLParserContext<'input>{
	/// Retrieves first TerminalNode corresponding to token STATE
	/// Returns `None` if there is no child corresponding to token STATE
	fn STATE(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(STATE, 0)
	}
	/// Retrieves first TerminalNode corresponding to token EQ
	/// Returns `None` if there is no child corresponding to token EQ
	fn EQ(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(EQ, 0)
	}
	fn ident(&self) -> Option<Rc<IdentContextAll<'input>>> where Self:Sized{
		self.child_of_type(0)
	}
}

impl<'input> ConstructorArgStateContextAttrs<'input> for ConstructorArgStateContext<'input>{}

pub struct ConstructorArgStateContextExt<'input>{
	__base:ConstructorArgContextExt<'input>,
	pub state: Option<Rc<IdentContextAll<'input>>>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{ConstructorArgStateContextExt<'a>}

impl<'input> LibSLParserContext<'input> for ConstructorArgStateContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for ConstructorArgStateContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_ConstructorArgState(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_ConstructorArgState(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for ConstructorArgStateContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_constructorArg }
	//fn type_rule_index() -> usize where Self: Sized { RULE_constructorArg }
}

impl<'input> Borrow<ConstructorArgContextExt<'input>> for ConstructorArgStateContext<'input>{
	fn borrow(&self) -> &ConstructorArgContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<ConstructorArgContextExt<'input>> for ConstructorArgStateContext<'input>{
	fn borrow_mut(&mut self) -> &mut ConstructorArgContextExt<'input> { &mut self.__base }
}

impl<'input> ConstructorArgContextAttrs<'input> for ConstructorArgStateContext<'input> {}

impl<'input> ConstructorArgStateContextExt<'input>{
	fn new(ctx: &dyn ConstructorArgContextAttrs<'input>) -> Rc<ConstructorArgContextAll<'input>>  {
		Rc::new(
			ConstructorArgContextAll::ConstructorArgStateContext(
				BaseParserRuleContext::copy_from(ctx,ConstructorArgStateContextExt{
        			state:None, 
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

pub type ConstructorArgVarContext<'input> = BaseParserRuleContext<'input,ConstructorArgVarContextExt<'input>>;

pub trait ConstructorArgVarContextAttrs<'input>: LibSLParserContext<'input>{
	/// Retrieves first TerminalNode corresponding to token EQ
	/// Returns `None` if there is no child corresponding to token EQ
	fn EQ(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
		self.get_token(EQ, 0)
	}
	fn ident(&self) -> Option<Rc<IdentContextAll<'input>>> where Self:Sized{
		self.child_of_type(0)
	}
	fn expr(&self) -> Option<Rc<ExprContextAll<'input>>> where Self:Sized{
		self.child_of_type(0)
	}
}

impl<'input> ConstructorArgVarContextAttrs<'input> for ConstructorArgVarContext<'input>{}

pub struct ConstructorArgVarContextExt<'input>{
	__base:ConstructorArgContextExt<'input>,
	pub name: Option<Rc<IdentContextAll<'input>>>,
	pub value: Option<Rc<ExprContextAll<'input>>>,
	__ph:PhantomData<&'input str>
}

antlr_rust::tid!{ConstructorArgVarContextExt<'a>}

impl<'input> LibSLParserContext<'input> for ConstructorArgVarContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for ConstructorArgVarContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_ConstructorArgVar(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_ConstructorArgVar(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for ConstructorArgVarContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_constructorArg }
	//fn type_rule_index() -> usize where Self: Sized { RULE_constructorArg }
}

impl<'input> Borrow<ConstructorArgContextExt<'input>> for ConstructorArgVarContext<'input>{
	fn borrow(&self) -> &ConstructorArgContextExt<'input> { &self.__base }
}
impl<'input> BorrowMut<ConstructorArgContextExt<'input>> for ConstructorArgVarContext<'input>{
	fn borrow_mut(&mut self) -> &mut ConstructorArgContextExt<'input> { &mut self.__base }
}

impl<'input> ConstructorArgContextAttrs<'input> for ConstructorArgVarContext<'input> {}

impl<'input> ConstructorArgVarContextExt<'input>{
	fn new(ctx: &dyn ConstructorArgContextAttrs<'input>) -> Rc<ConstructorArgContextAll<'input>>  {
		Rc::new(
			ConstructorArgContextAll::ConstructorArgVarContext(
				BaseParserRuleContext::copy_from(ctx,ConstructorArgVarContextExt{
        			name:None, value:None, 
        			__base: ctx.borrow().clone(),
        			__ph:PhantomData
				})
			)
		)
	}
}

impl<'input, I, H> LibSLParser<'input, I, H>
where
    I: TokenStream<'input, TF = LocalTokenFactory<'input> > + TidAble<'input>,
    H: ErrorStrategy<'input,BaseParserType<'input,I>>
{
	pub fn constructorArg(&mut self,)
	-> Result<Rc<ConstructorArgContextAll<'input>>,ANTLRError> {
		let mut recog = self;
		let _parentctx = recog.ctx.take();
		let mut _localctx = ConstructorArgContextExt::new(_parentctx.clone(), recog.base.get_state());
        recog.base.enter_rule(_localctx.clone(), 202, RULE_constructorArg);
        let mut _localctx: Rc<ConstructorArgContextAll> = _localctx;
		let result: Result<(), ANTLRError> = (|| {

			recog.base.set_state(1358);
			recog.err_handler.sync(&mut recog.base)?;
			match recog.base.input.la(1) {
			 STATE 
				=> {
					let tmp = ConstructorArgStateContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 1);
					_localctx = tmp;
					{
					recog.base.set_state(1351);
					recog.base.match_token(STATE,&mut recog.err_handler)?;

					recog.base.set_state(1352);
					recog.base.match_token(EQ,&mut recog.err_handler)?;

					/*InvokeRule ident*/
					recog.base.set_state(1353);
					let tmp = recog.ident()?;
					if let ConstructorArgContextAll::ConstructorArgStateContext(ctx) = cast_mut::<_,ConstructorArgContextAll >(&mut _localctx){
					ctx.state = Some(tmp.clone()); } else {unreachable!("cant cast");}  

					}
				}

			 IMPLEMENTS | STATIC | PURE | Identifier 
				=> {
					let tmp = ConstructorArgVarContextExt::new(&**_localctx);
					recog.base.enter_outer_alt(Some(tmp.clone()), 2);
					_localctx = tmp;
					{
					/*InvokeRule ident*/
					recog.base.set_state(1354);
					let tmp = recog.ident()?;
					if let ConstructorArgContextAll::ConstructorArgVarContext(ctx) = cast_mut::<_,ConstructorArgContextAll >(&mut _localctx){
					ctx.name = Some(tmp.clone()); } else {unreachable!("cant cast");}  

					recog.base.set_state(1355);
					recog.base.match_token(EQ,&mut recog.err_handler)?;

					/*InvokeRule expr*/
					recog.base.set_state(1356);
					let tmp = recog.expr_rec(0)?;
					if let ConstructorArgContextAll::ConstructorArgVarContext(ctx) = cast_mut::<_,ConstructorArgContextAll >(&mut _localctx){
					ctx.value = Some(tmp.clone()); } else {unreachable!("cant cast");}  

					}
				}

				_ => Err(ANTLRError::NoAltError(NoViableAltError::new(&mut recog.base)))?
			}
			Ok(())
		})();
		match result {
		Ok(_)=>{},
        Err(e @ ANTLRError::FallThrough(_)) => return Err(e),
		Err(ref re) => {
				//_localctx.exception = re;
				recog.err_handler.report_error(&mut recog.base, re);
				recog.err_handler.recover(&mut recog.base, re)?;
			}
		}
		recog.base.exit_rule();

		Ok(_localctx)
	}
}
//------------------- ident ----------------
pub type IdentContextAll<'input> = IdentContext<'input>;


pub type IdentContext<'input> = BaseParserRuleContext<'input,IdentContextExt<'input>>;

#[derive(Clone)]
pub struct IdentContextExt<'input>{
ph:PhantomData<&'input str>
}

impl<'input> LibSLParserContext<'input> for IdentContext<'input>{}

impl<'input,'a> Listenable<dyn LibSLParserListener<'input> + 'a> for IdentContext<'input>{
		fn enter(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.enter_every_rule(self);
			listener.enter_ident(self);
		}fn exit(&self,listener: &mut (dyn LibSLParserListener<'input> + 'a)) {
			listener.exit_ident(self);
			listener.exit_every_rule(self);
		}
}

impl<'input> CustomRuleContext<'input> for IdentContextExt<'input>{
	type TF = LocalTokenFactory<'input>;
	type Ctx = LibSLParserContextType;
	fn get_rule_index(&self) -> usize { RULE_ident }
	//fn type_rule_index() -> usize where Self: Sized { RULE_ident }
}
antlr_rust::tid!{IdentContextExt<'a>}

impl<'input> IdentContextExt<'input>{
	fn new(parent: Option<Rc<dyn LibSLParserContext<'input> + 'input > >, invoking_state: isize) -> Rc<IdentContextAll<'input>> {
		Rc::new(
			BaseParserRuleContext::new_parser_ctx(parent, invoking_state,IdentContextExt{
				ph:PhantomData
			}),
		)
	}
}

pub trait IdentContextAttrs<'input>: LibSLParserContext<'input> + BorrowMut<IdentContextExt<'input>>{

/// Retrieves first TerminalNode corresponding to token Identifier
/// Returns `None` if there is no child corresponding to token Identifier
fn Identifier(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(Identifier, 0)
}
/// Retrieves first TerminalNode corresponding to token STATIC
/// Returns `None` if there is no child corresponding to token STATIC
fn STATIC(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(STATIC, 0)
}
/// Retrieves first TerminalNode corresponding to token IMPLEMENTS
/// Returns `None` if there is no child corresponding to token IMPLEMENTS
fn IMPLEMENTS(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(IMPLEMENTS, 0)
}
/// Retrieves first TerminalNode corresponding to token PURE
/// Returns `None` if there is no child corresponding to token PURE
fn PURE(&self) -> Option<Rc<TerminalNode<'input,LibSLParserContextType>>> where Self:Sized{
	self.get_token(PURE, 0)
}

}

impl<'input> IdentContextAttrs<'input> for IdentContext<'input>{}

impl<'input, I, H> LibSLParser<'input, I, H>
where
    I: TokenStream<'input, TF = LocalTokenFactory<'input> > + TidAble<'input>,
    H: ErrorStrategy<'input,BaseParserType<'input,I>>
{
	pub fn ident(&mut self,)
	-> Result<Rc<IdentContextAll<'input>>,ANTLRError> {
		let mut recog = self;
		let _parentctx = recog.ctx.take();
		let mut _localctx = IdentContextExt::new(_parentctx.clone(), recog.base.get_state());
        recog.base.enter_rule(_localctx.clone(), 204, RULE_ident);
        let mut _localctx: Rc<IdentContextAll> = _localctx;
		let mut _la: isize = -1;
		let result: Result<(), ANTLRError> = (|| {

			//recog.base.enter_outer_alt(_localctx.clone(), 1);
			recog.base.enter_outer_alt(None, 1);
			{
			recog.base.set_state(1360);
			_la = recog.base.input.la(1);
			if { !(((((_la - 86)) & !0x3f) == 0 && ((1usize << (_la - 86)) & 519) != 0)) } {
				recog.err_handler.recover_inline(&mut recog.base)?;

			}
			else {
				if  recog.base.input.la(1)==TOKEN_EOF { recog.base.matched_eof = true };
				recog.err_handler.report_match(&mut recog.base);
				recog.base.consume(&mut recog.err_handler);
			}
			}
			Ok(())
		})();
		match result {
		Ok(_)=>{},
        Err(e @ ANTLRError::FallThrough(_)) => return Err(e),
		Err(ref re) => {
				//_localctx.exception = re;
				recog.err_handler.report_error(&mut recog.base, re);
				recog.err_handler.recover(&mut recog.base, re)?;
			}
		}
		recog.base.exit_rule();

		Ok(_localctx)
	}
}

static _ATN: LazyLock<Arc<ATN>> = LazyLock::new(||
	Arc::new(ATNDeserializer::new(None).deserialize(_serializedATN))
);

static _decision_to_DFA: LazyLock<Arc<Vec<antlr_rust::RwLock<DFA>>>> = LazyLock::new(|| {
	let mut dfa = Vec::new();
	let size = _ATN.decision_to_state.len();
	for i in 0..size {
		dfa.push(DFA::new(
			_ATN.clone(),
			_ATN.get_decision_state(i),
			i as isize,
		).into())
	}
	Arc::new(dfa)
});

const _serializedATN: &'static [isize] = &[
    4,1,101,1363,2,0,7,0,2,1,7,1,2,2,7,2,2,3,7,3,2,4,7,4,2,5,7,5,2,6,7,6,
    2,7,7,7,2,8,7,8,2,9,7,9,2,10,7,10,2,11,7,11,2,12,7,12,2,13,7,13,2,14,
    7,14,2,15,7,15,2,16,7,16,2,17,7,17,2,18,7,18,2,19,7,19,2,20,7,20,2,21,
    7,21,2,22,7,22,2,23,7,23,2,24,7,24,2,25,7,25,2,26,7,26,2,27,7,27,2,28,
    7,28,2,29,7,29,2,30,7,30,2,31,7,31,2,32,7,32,2,33,7,33,2,34,7,34,2,35,
    7,35,2,36,7,36,2,37,7,37,2,38,7,38,2,39,7,39,2,40,7,40,2,41,7,41,2,42,
    7,42,2,43,7,43,2,44,7,44,2,45,7,45,2,46,7,46,2,47,7,47,2,48,7,48,2,49,
    7,49,2,50,7,50,2,51,7,51,2,52,7,52,2,53,7,53,2,54,7,54,2,55,7,55,2,56,
    7,56,2,57,7,57,2,58,7,58,2,59,7,59,2,60,7,60,2,61,7,61,2,62,7,62,2,63,
    7,63,2,64,7,64,2,65,7,65,2,66,7,66,2,67,7,67,2,68,7,68,2,69,7,69,2,70,
    7,70,2,71,7,71,2,72,7,72,2,73,7,73,2,74,7,74,2,75,7,75,2,76,7,76,2,77,
    7,77,2,78,7,78,2,79,7,79,2,80,7,80,2,81,7,81,2,82,7,82,2,83,7,83,2,84,
    7,84,2,85,7,85,2,86,7,86,2,87,7,87,2,88,7,88,2,89,7,89,2,90,7,90,2,91,
    7,91,2,92,7,92,2,93,7,93,2,94,7,94,2,95,7,95,2,96,7,96,2,97,7,97,2,98,
    7,98,2,99,7,99,2,100,7,100,2,101,7,101,2,102,7,102,1,0,3,0,208,8,0,1,
    0,5,0,211,8,0,10,0,12,0,214,9,0,1,0,1,0,1,1,1,1,1,1,1,1,1,1,1,1,1,1,
    3,1,225,8,1,1,1,1,1,3,1,229,8,1,1,1,1,1,3,1,233,8,1,1,1,1,1,1,2,1,2,
    1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,3,2,250,8,2,1,3,1,3,1,3,
    1,3,1,4,1,4,1,4,1,4,1,5,1,5,3,5,262,8,5,1,6,1,6,1,6,5,6,267,8,6,10,6,
    12,6,270,9,6,1,6,1,6,1,7,5,7,275,8,7,10,7,12,7,278,9,7,1,7,1,7,1,7,1,
    7,1,7,1,7,1,8,1,8,1,8,5,8,289,8,8,10,8,12,8,292,9,8,1,8,3,8,295,8,8,
    1,9,1,9,1,9,1,9,1,9,1,10,5,10,303,8,10,10,10,12,10,306,9,10,1,10,1,10,
    1,10,1,10,1,10,1,10,1,11,5,11,315,8,11,10,11,12,11,318,9,11,1,11,1,11,
    1,11,3,11,323,8,11,1,11,3,11,326,8,11,1,11,1,11,5,11,330,8,11,10,11,
    12,11,333,9,11,1,11,3,11,336,8,11,1,12,1,12,3,12,340,8,12,1,12,1,12,
    1,12,3,12,345,8,12,1,13,1,13,1,13,1,13,3,13,351,8,13,1,14,5,14,354,8,
    14,10,14,12,14,357,9,14,1,14,1,14,1,14,1,14,5,14,363,8,14,10,14,12,14,
    366,9,14,1,14,1,14,1,15,1,15,1,15,1,15,1,15,1,16,3,16,376,8,16,1,16,
    1,16,1,17,1,17,3,17,382,8,17,1,18,1,18,1,18,1,18,1,18,3,18,389,8,18,
    3,18,391,8,18,1,18,1,18,1,18,1,19,1,19,1,19,5,19,399,8,19,10,19,12,19,
    402,9,19,1,20,1,20,1,20,1,20,1,20,3,20,409,8,20,1,21,5,21,412,8,21,10,
    21,12,21,415,9,21,1,21,1,21,1,21,1,21,3,21,421,8,21,1,21,1,21,1,21,3,
    21,426,8,21,3,21,428,8,21,1,21,1,21,1,21,3,21,433,8,21,1,21,3,21,436,
    8,21,1,21,1,21,1,22,1,22,1,22,5,22,443,8,22,10,22,12,22,446,9,22,1,23,
    5,23,449,8,23,10,23,12,23,452,9,23,1,23,1,23,1,23,1,23,1,24,5,24,459,
    8,24,10,24,12,24,462,9,24,1,24,1,24,3,24,466,8,24,1,24,1,24,1,24,1,24,
    3,24,472,8,24,3,24,474,8,24,1,24,3,24,477,8,24,1,24,1,24,1,24,1,24,3,
    24,483,8,24,5,24,485,8,24,10,24,12,24,488,9,24,1,24,3,24,491,8,24,1,
    24,1,24,5,24,495,8,24,10,24,12,24,498,9,24,1,24,1,24,1,25,1,25,1,25,
    5,25,505,8,25,10,25,12,25,508,9,25,1,26,5,26,511,8,26,10,26,12,26,514,
    9,26,1,26,1,26,1,26,1,26,1,26,1,26,3,26,522,8,26,1,27,1,27,1,27,1,27,
    5,27,528,8,27,10,27,12,27,531,9,27,1,28,1,28,1,28,1,28,1,28,1,28,1,28,
    1,28,3,28,541,8,28,1,29,5,29,544,8,29,10,29,12,29,547,9,29,1,29,5,29,
    550,8,29,10,29,12,29,553,9,29,1,29,1,29,1,29,1,29,3,29,559,8,29,1,29,
    3,29,562,8,29,1,29,1,29,3,29,566,8,29,1,29,1,29,1,29,3,29,571,8,29,3,
    29,573,8,29,1,29,1,29,1,29,3,29,578,8,29,1,29,3,29,581,8,29,1,29,1,29,
    1,30,1,30,1,31,1,31,1,31,1,32,1,32,1,32,1,32,1,32,3,32,595,8,32,3,32,
    597,8,32,1,33,5,33,600,8,33,10,33,12,33,603,9,33,1,33,1,33,1,33,3,33,
    608,8,33,1,33,1,33,1,33,3,33,613,8,33,3,33,615,8,33,1,33,1,33,3,33,619,
    8,33,1,33,3,33,622,8,33,1,34,5,34,625,8,34,10,34,12,34,628,9,34,1,34,
    1,34,1,34,1,34,3,34,634,8,34,1,34,1,34,3,34,638,8,34,1,34,1,34,1,35,
    1,35,3,35,644,8,35,1,36,1,36,1,36,1,36,1,37,1,37,1,37,3,37,653,8,37,
    1,38,1,38,1,38,5,38,658,8,38,10,38,12,38,661,9,38,1,39,1,39,1,39,1,39,
    1,39,1,39,1,39,1,39,1,40,1,40,1,40,1,40,3,40,675,8,40,3,40,677,8,40,
    1,40,3,40,680,8,40,1,41,1,41,1,41,1,41,3,41,686,8,41,3,41,688,8,41,1,
    41,3,41,691,8,41,1,42,1,42,1,42,5,42,696,8,42,10,42,12,42,699,9,42,1,
    43,1,43,1,43,1,43,1,43,3,43,706,8,43,3,43,708,8,43,1,43,1,43,3,43,712,
    8,43,1,44,5,44,715,8,44,10,44,12,44,718,9,44,1,44,1,44,3,44,722,8,44,
    1,44,3,44,725,8,44,1,44,1,44,1,44,3,44,730,8,44,3,44,732,8,44,1,44,1,
    44,1,44,3,44,737,8,44,1,44,1,44,1,45,5,45,742,8,45,10,45,12,45,745,9,
    45,1,45,1,45,3,45,749,8,45,1,45,3,45,752,8,45,1,45,1,45,1,45,3,45,757,
    8,45,3,45,759,8,45,1,45,1,45,1,45,3,45,764,8,45,1,45,1,45,1,46,5,46,
    769,8,46,10,46,12,46,772,9,46,1,46,5,46,775,8,46,10,46,12,46,778,9,46,
    1,46,1,46,3,46,782,8,46,1,46,1,46,3,46,786,8,46,1,46,1,46,1,46,3,46,
    791,8,46,3,46,793,8,46,1,46,1,46,1,46,3,46,798,8,46,1,46,3,46,801,8,
    46,1,46,1,46,1,47,1,47,1,48,1,48,1,48,5,48,810,8,48,10,48,12,48,813,
    9,48,1,49,5,49,816,8,49,10,49,12,49,819,9,49,1,49,1,49,1,49,1,49,1,50,
    5,50,826,8,50,10,50,12,50,829,9,50,1,50,5,50,832,8,50,10,50,12,50,835,
    9,50,1,51,1,51,1,51,3,51,840,8,51,1,52,1,52,1,52,1,52,3,52,846,8,52,
    1,52,1,52,1,53,1,53,1,53,1,53,3,53,854,8,53,1,53,1,53,1,54,1,54,1,54,
    1,54,3,54,862,8,54,1,54,1,54,1,54,1,55,1,55,1,55,1,55,1,55,3,55,872,
    8,55,1,56,1,56,3,56,876,8,56,1,57,1,57,1,57,1,57,1,57,1,57,1,57,1,57,
    1,57,1,57,3,57,888,8,57,1,58,1,58,5,58,892,8,58,10,58,12,58,895,9,58,
    1,58,1,58,1,59,1,59,1,59,1,59,1,59,1,59,1,59,3,59,906,8,59,1,60,1,60,
    1,60,1,60,1,60,3,60,913,8,60,3,60,915,8,60,1,60,3,60,918,8,60,1,61,1,
    61,1,61,5,61,923,8,61,10,61,12,61,926,9,61,1,62,1,62,1,62,3,62,931,8,
    62,1,62,1,62,1,63,1,63,3,63,937,8,63,1,64,1,64,1,64,5,64,942,8,64,10,
    64,12,64,945,9,64,1,65,1,65,1,65,1,65,5,65,951,8,65,10,65,12,65,954,
    9,65,1,65,3,65,957,8,65,1,66,1,66,1,66,1,66,1,67,1,67,1,67,3,67,966,
    8,67,3,67,968,8,67,1,67,1,67,1,68,1,68,1,68,5,68,975,8,68,10,68,12,68,
    978,9,68,1,69,3,69,981,8,69,1,69,1,69,1,70,1,70,1,70,1,70,3,70,989,8,
    70,1,71,1,71,1,71,5,71,994,8,71,10,71,12,71,997,9,71,1,72,1,72,1,72,
    1,72,1,72,1,72,1,72,3,72,1006,8,72,1,73,1,73,1,73,1,73,1,73,1,73,1,73,
    1,73,1,73,5,73,1017,8,73,10,73,12,73,1020,9,73,1,74,1,74,3,74,1024,8,
    74,1,75,1,75,1,75,1,76,1,76,1,76,3,76,1032,8,76,3,76,1034,8,76,1,76,
    1,76,1,77,1,77,1,77,5,77,1041,8,77,10,77,12,77,1044,9,77,1,78,3,78,1047,
    8,78,1,78,1,78,3,78,1051,8,78,1,79,1,79,1,79,5,79,1056,8,79,10,79,12,
    79,1059,9,79,1,79,3,79,1062,8,79,1,80,1,80,1,80,1,80,1,80,1,80,1,80,
    3,80,1071,8,80,1,81,1,81,1,81,1,81,1,81,1,81,1,81,3,81,1080,8,81,1,82,
    1,82,1,82,1,82,1,82,1,83,1,83,1,83,1,83,1,83,1,83,1,83,1,83,1,83,1,83,
    3,83,1097,8,83,1,84,1,84,1,84,1,85,1,85,1,85,1,85,1,85,1,85,1,85,1,85,
    1,85,1,85,1,85,3,85,1113,8,85,1,86,1,86,1,86,5,86,1118,8,86,10,86,12,
    86,1121,9,86,1,87,1,87,1,87,1,87,1,87,1,87,1,87,1,87,1,87,3,87,1132,
    8,87,1,88,1,88,1,88,1,88,1,88,1,88,3,88,1140,8,88,1,89,1,89,1,89,1,89,
    1,89,1,89,1,89,1,89,1,89,1,89,3,89,1152,8,89,1,89,1,89,1,89,3,89,1157,
    8,89,3,89,1159,8,89,1,89,1,89,1,89,1,89,1,89,1,89,1,89,1,89,3,89,1169,
    8,89,1,89,1,89,1,89,1,89,1,89,1,89,1,89,1,89,1,89,1,89,1,89,1,89,1,89,
    1,89,1,89,1,89,1,89,1,89,1,89,1,89,1,89,1,89,1,89,1,89,1,89,1,89,1,89,
    1,89,1,89,1,89,1,89,1,89,1,89,1,89,1,89,1,89,1,89,3,89,1208,8,89,1,89,
    1,89,1,89,3,89,1213,8,89,3,89,1215,8,89,1,89,1,89,1,89,1,89,1,89,1,89,
    1,89,1,89,1,89,1,89,1,89,1,89,1,89,1,89,1,89,3,89,1232,8,89,1,89,1,89,
    1,89,1,89,3,89,1238,8,89,1,89,1,89,1,89,1,89,1,89,5,89,1245,8,89,10,
    89,12,89,1248,9,89,1,90,1,90,1,90,1,90,3,90,1254,8,90,1,91,1,91,1,91,
    3,91,1259,8,91,1,92,1,92,3,92,1263,8,92,1,93,1,93,1,93,1,93,1,93,1,93,
    1,93,1,93,1,93,1,93,3,93,1275,8,93,1,94,1,94,1,94,1,94,1,94,1,94,1,94,
    3,94,1284,8,94,1,94,3,94,1287,8,94,1,95,1,95,1,95,1,95,1,95,1,95,1,95,
    3,95,1296,8,95,1,96,1,96,1,96,3,96,1301,8,96,3,96,1303,8,96,1,96,1,96,
    1,97,1,97,1,97,3,97,1310,8,97,3,97,1312,8,97,1,97,1,97,1,98,1,98,1,98,
    3,98,1319,8,98,1,98,1,98,1,98,3,98,1324,8,98,3,98,1326,8,98,1,98,1,98,
    1,99,1,99,1,99,3,99,1333,8,99,1,99,1,99,1,99,3,99,1338,8,99,3,99,1340,
    8,99,1,99,1,99,1,100,1,100,1,100,5,100,1347,8,100,10,100,12,100,1350,
    9,100,1,101,1,101,1,101,1,101,1,101,1,101,1,101,3,101,1359,8,101,1,102,
    1,102,1,102,0,2,146,178,103,0,2,4,6,8,10,12,14,16,18,20,22,24,26,28,
    30,32,34,36,38,40,42,44,46,48,50,52,54,56,58,60,62,64,66,68,70,72,74,
    76,78,80,82,84,86,88,90,92,94,96,98,100,102,104,106,108,110,112,114,
    116,118,120,122,124,126,128,130,132,134,136,138,140,142,144,146,148,
    150,152,154,156,158,160,162,164,166,168,170,172,174,176,178,180,182,
    184,186,188,190,192,194,196,198,200,202,204,0,1,2,0,86,88,95,95,1520,
    0,207,1,0,0,0,2,217,1,0,0,0,4,249,1,0,0,0,6,251,1,0,0,0,8,255,1,0,0,
    0,10,261,1,0,0,0,12,263,1,0,0,0,14,276,1,0,0,0,16,294,1,0,0,0,18,296,
    1,0,0,0,20,304,1,0,0,0,22,316,1,0,0,0,24,339,1,0,0,0,26,350,1,0,0,0,
    28,355,1,0,0,0,30,369,1,0,0,0,32,375,1,0,0,0,34,381,1,0,0,0,36,383,1,
    0,0,0,38,395,1,0,0,0,40,403,1,0,0,0,42,413,1,0,0,0,44,439,1,0,0,0,46,
    450,1,0,0,0,48,460,1,0,0,0,50,501,1,0,0,0,52,512,1,0,0,0,54,523,1,0,
    0,0,56,540,1,0,0,0,58,545,1,0,0,0,60,584,1,0,0,0,62,586,1,0,0,0,64,596,
    1,0,0,0,66,601,1,0,0,0,68,626,1,0,0,0,70,643,1,0,0,0,72,645,1,0,0,0,
    74,652,1,0,0,0,76,654,1,0,0,0,78,662,1,0,0,0,80,679,1,0,0,0,82,690,1,
    0,0,0,84,692,1,0,0,0,86,711,1,0,0,0,88,716,1,0,0,0,90,743,1,0,0,0,92,
    770,1,0,0,0,94,804,1,0,0,0,96,806,1,0,0,0,98,817,1,0,0,0,100,827,1,0,
    0,0,102,839,1,0,0,0,104,841,1,0,0,0,106,849,1,0,0,0,108,857,1,0,0,0,
    110,871,1,0,0,0,112,875,1,0,0,0,114,887,1,0,0,0,116,889,1,0,0,0,118,
    898,1,0,0,0,120,907,1,0,0,0,122,919,1,0,0,0,124,930,1,0,0,0,126,934,
    1,0,0,0,128,938,1,0,0,0,130,946,1,0,0,0,132,958,1,0,0,0,134,962,1,0,
    0,0,136,971,1,0,0,0,138,980,1,0,0,0,140,988,1,0,0,0,142,990,1,0,0,0,
    144,1005,1,0,0,0,146,1007,1,0,0,0,148,1021,1,0,0,0,150,1025,1,0,0,0,
    152,1028,1,0,0,0,154,1037,1,0,0,0,156,1050,1,0,0,0,158,1061,1,0,0,0,
    160,1070,1,0,0,0,162,1072,1,0,0,0,164,1081,1,0,0,0,166,1096,1,0,0,0,
    168,1098,1,0,0,0,170,1112,1,0,0,0,172,1114,1,0,0,0,174,1131,1,0,0,0,
    176,1139,1,0,0,0,178,1168,1,0,0,0,180,1253,1,0,0,0,182,1258,1,0,0,0,
    184,1262,1,0,0,0,186,1274,1,0,0,0,188,1286,1,0,0,0,190,1295,1,0,0,0,
    192,1297,1,0,0,0,194,1306,1,0,0,0,196,1315,1,0,0,0,198,1329,1,0,0,0,
    200,1343,1,0,0,0,202,1358,1,0,0,0,204,1360,1,0,0,0,206,208,3,2,1,0,207,
    206,1,0,0,0,207,208,1,0,0,0,208,212,1,0,0,0,209,211,3,4,2,0,210,209,
    1,0,0,0,211,214,1,0,0,0,212,210,1,0,0,0,212,213,1,0,0,0,213,215,1,0,
    0,0,214,212,1,0,0,0,215,216,5,0,0,1,216,1,1,0,0,0,217,218,5,45,0,0,218,
    219,5,96,0,0,219,220,5,1,0,0,220,221,5,46,0,0,221,224,3,204,102,0,222,
    223,5,47,0,0,223,225,5,96,0,0,224,222,1,0,0,0,224,225,1,0,0,0,225,228,
    1,0,0,0,226,227,5,48,0,0,227,229,5,96,0,0,228,226,1,0,0,0,228,229,1,
    0,0,0,229,232,1,0,0,0,230,231,5,49,0,0,231,233,5,96,0,0,232,230,1,0,
    0,0,232,233,1,0,0,0,233,234,1,0,0,0,234,235,5,1,0,0,235,3,1,0,0,0,236,
    250,3,6,3,0,237,250,3,8,4,0,238,250,3,12,6,0,239,250,3,20,10,0,240,250,
    3,22,11,0,241,250,3,28,14,0,242,250,3,36,18,0,243,250,3,42,21,0,244,
    250,3,48,24,0,245,250,3,58,29,0,246,250,3,92,46,0,247,250,3,66,33,0,
    248,250,3,68,34,0,249,236,1,0,0,0,249,237,1,0,0,0,249,238,1,0,0,0,249,
    239,1,0,0,0,249,240,1,0,0,0,249,241,1,0,0,0,249,242,1,0,0,0,249,243,
    1,0,0,0,249,244,1,0,0,0,249,245,1,0,0,0,249,246,1,0,0,0,249,247,1,0,
    0,0,249,248,1,0,0,0,250,5,1,0,0,0,251,252,5,43,0,0,252,253,3,10,5,0,
    253,254,5,1,0,0,254,7,1,0,0,0,255,256,5,44,0,0,256,257,3,10,5,0,257,
    258,5,1,0,0,258,9,1,0,0,0,259,262,5,96,0,0,260,262,5,101,0,0,261,259,
    1,0,0,0,261,260,1,0,0,0,262,11,1,0,0,0,263,264,5,52,0,0,264,268,5,4,
    0,0,265,267,3,14,7,0,266,265,1,0,0,0,267,270,1,0,0,0,268,266,1,0,0,0,
    268,269,1,0,0,0,269,271,1,0,0,0,270,268,1,0,0,0,271,272,5,5,0,0,272,
    13,1,0,0,0,273,275,3,120,60,0,274,273,1,0,0,0,275,278,1,0,0,0,276,274,
    1,0,0,0,276,277,1,0,0,0,277,279,1,0,0,0,278,276,1,0,0,0,279,280,3,126,
    63,0,280,281,5,6,0,0,281,282,3,146,73,0,282,283,5,7,0,0,283,284,3,16,
    8,0,284,15,1,0,0,0,285,295,5,1,0,0,286,290,5,4,0,0,287,289,3,18,9,0,
    288,287,1,0,0,0,289,292,1,0,0,0,290,288,1,0,0,0,290,291,1,0,0,0,291,
    293,1,0,0,0,292,290,1,0,0,0,293,295,5,5,0,0,294,285,1,0,0,0,294,286,
    1,0,0,0,295,17,1,0,0,0,296,297,3,204,102,0,297,298,5,11,0,0,298,299,
    3,174,87,0,299,300,5,1,0,0,300,19,1,0,0,0,301,303,3,120,60,0,302,301,
    1,0,0,0,303,306,1,0,0,0,304,302,1,0,0,0,304,305,1,0,0,0,305,307,1,0,
    0,0,306,304,1,0,0,0,307,308,5,50,0,0,308,309,3,126,63,0,309,310,5,2,
    0,0,310,311,3,146,73,0,311,312,5,1,0,0,312,21,1,0,0,0,313,315,3,120,
    60,0,314,313,1,0,0,0,315,318,1,0,0,0,316,314,1,0,0,0,316,317,1,0,0,0,
    317,319,1,0,0,0,318,316,1,0,0,0,319,320,5,51,0,0,320,322,3,126,63,0,
    321,323,3,24,12,0,322,321,1,0,0,0,322,323,1,0,0,0,323,325,1,0,0,0,324,
    326,3,130,65,0,325,324,1,0,0,0,325,326,1,0,0,0,326,335,1,0,0,0,327,331,
    5,4,0,0,328,330,3,26,13,0,329,328,1,0,0,0,330,333,1,0,0,0,331,329,1,
    0,0,0,331,332,1,0,0,0,332,334,1,0,0,0,333,331,1,0,0,0,334,336,5,5,0,
    0,335,327,1,0,0,0,335,336,1,0,0,0,336,23,1,0,0,0,337,338,5,79,0,0,338,
    340,3,146,73,0,339,337,1,0,0,0,339,340,1,0,0,0,340,341,1,0,0,0,341,342,
    5,85,0,0,342,344,3,142,71,0,343,345,5,12,0,0,344,343,1,0,0,0,344,345,
    1,0,0,0,345,25,1,0,0,0,346,351,3,68,34,0,347,351,3,58,29,0,348,351,3,
    92,46,0,349,351,3,66,33,0,350,346,1,0,0,0,350,347,1,0,0,0,350,348,1,
    0,0,0,350,349,1,0,0,0,351,27,1,0,0,0,352,354,3,120,60,0,353,352,1,0,
    0,0,354,357,1,0,0,0,355,353,1,0,0,0,355,356,1,0,0,0,356,358,1,0,0,0,
    357,355,1,0,0,0,358,359,5,53,0,0,359,360,3,126,63,0,360,364,5,4,0,0,
    361,363,3,30,15,0,362,361,1,0,0,0,363,366,1,0,0,0,364,362,1,0,0,0,364,
    365,1,0,0,0,365,367,1,0,0,0,366,364,1,0,0,0,367,368,5,5,0,0,368,29,1,
    0,0,0,369,370,3,204,102,0,370,371,5,2,0,0,371,372,3,32,16,0,372,373,
    5,1,0,0,373,31,1,0,0,0,374,376,3,34,17,0,375,374,1,0,0,0,375,376,1,0,
    0,0,376,377,1,0,0,0,377,378,5,92,0,0,378,33,1,0,0,0,379,382,5,20,0,0,
    380,382,5,19,0,0,381,379,1,0,0,0,381,380,1,0,0,0,382,35,1,0,0,0,383,
    384,5,54,0,0,384,385,3,204,102,0,385,390,5,6,0,0,386,388,3,38,19,0,387,
    389,5,12,0,0,388,387,1,0,0,0,388,389,1,0,0,0,389,391,1,0,0,0,390,386,
    1,0,0,0,390,391,1,0,0,0,391,392,1,0,0,0,392,393,5,7,0,0,393,394,5,1,
    0,0,394,37,1,0,0,0,395,400,3,40,20,0,396,397,5,12,0,0,397,399,3,40,20,
    0,398,396,1,0,0,0,399,402,1,0,0,0,400,398,1,0,0,0,400,401,1,0,0,0,401,
    39,1,0,0,0,402,400,1,0,0,0,403,404,3,204,102,0,404,405,5,11,0,0,405,
    408,3,146,73,0,406,407,5,2,0,0,407,409,3,178,89,0,408,406,1,0,0,0,408,
    409,1,0,0,0,409,41,1,0,0,0,410,412,3,120,60,0,411,410,1,0,0,0,412,415,
    1,0,0,0,413,411,1,0,0,0,413,414,1,0,0,0,414,416,1,0,0,0,415,413,1,0,
    0,0,416,417,5,75,0,0,417,418,5,69,0,0,418,420,3,204,102,0,419,421,3,
    134,67,0,420,419,1,0,0,0,420,421,1,0,0,0,421,422,1,0,0,0,422,427,5,6,
    0,0,423,425,3,44,22,0,424,426,5,12,0,0,425,424,1,0,0,0,425,426,1,0,0,
    0,426,428,1,0,0,0,427,423,1,0,0,0,427,428,1,0,0,0,428,429,1,0,0,0,429,
    432,5,7,0,0,430,431,5,11,0,0,431,433,3,146,73,0,432,430,1,0,0,0,432,
    433,1,0,0,0,433,435,1,0,0,0,434,436,3,130,65,0,435,434,1,0,0,0,435,436,
    1,0,0,0,436,437,1,0,0,0,437,438,5,1,0,0,438,43,1,0,0,0,439,444,3,46,
    23,0,440,441,5,12,0,0,441,443,3,46,23,0,442,440,1,0,0,0,443,446,1,0,
    0,0,444,442,1,0,0,0,444,445,1,0,0,0,445,45,1,0,0,0,446,444,1,0,0,0,447,
    449,3,120,60,0,448,447,1,0,0,0,449,452,1,0,0,0,450,448,1,0,0,0,450,451,
    1,0,0,0,451,453,1,0,0,0,452,450,1,0,0,0,453,454,3,204,102,0,454,455,
    5,11,0,0,455,456,3,146,73,0,456,47,1,0,0,0,457,459,3,120,60,0,458,457,
    1,0,0,0,459,462,1,0,0,0,460,458,1,0,0,0,460,461,1,0,0,0,461,463,1,0,
    0,0,462,460,1,0,0,0,463,465,5,55,0,0,464,466,5,56,0,0,465,464,1,0,0,
    0,465,466,1,0,0,0,466,467,1,0,0,0,467,476,3,126,63,0,468,473,5,6,0,0,
    469,471,3,50,25,0,470,472,5,12,0,0,471,470,1,0,0,0,471,472,1,0,0,0,472,
    474,1,0,0,0,473,469,1,0,0,0,473,474,1,0,0,0,474,475,1,0,0,0,475,477,
    5,7,0,0,476,468,1,0,0,0,476,477,1,0,0,0,477,478,1,0,0,0,478,479,5,11,
    0,0,479,486,3,146,73,0,480,482,3,54,27,0,481,483,5,12,0,0,482,481,1,
    0,0,0,482,483,1,0,0,0,483,485,1,0,0,0,484,480,1,0,0,0,485,488,1,0,0,
    0,486,484,1,0,0,0,486,487,1,0,0,0,487,490,1,0,0,0,488,486,1,0,0,0,489,
    491,3,130,65,0,490,489,1,0,0,0,490,491,1,0,0,0,491,492,1,0,0,0,492,496,
    5,4,0,0,493,495,3,56,28,0,494,493,1,0,0,0,495,498,1,0,0,0,496,494,1,
    0,0,0,496,497,1,0,0,0,497,499,1,0,0,0,498,496,1,0,0,0,499,500,5,5,0,
    0,500,49,1,0,0,0,501,506,3,52,26,0,502,503,5,12,0,0,503,505,3,52,26,
    0,504,502,1,0,0,0,505,508,1,0,0,0,506,504,1,0,0,0,506,507,1,0,0,0,507,
    51,1,0,0,0,508,506,1,0,0,0,509,511,3,120,60,0,510,509,1,0,0,0,511,514,
    1,0,0,0,512,510,1,0,0,0,512,513,1,0,0,0,513,515,1,0,0,0,514,512,1,0,
    0,0,515,516,3,70,35,0,516,517,3,204,102,0,517,518,5,11,0,0,518,521,3,
    146,73,0,519,520,5,2,0,0,520,522,3,178,89,0,521,519,1,0,0,0,521,522,
    1,0,0,0,522,53,1,0,0,0,523,524,5,86,0,0,524,529,3,204,102,0,525,526,
    5,12,0,0,526,528,3,204,102,0,527,525,1,0,0,0,528,531,1,0,0,0,529,527,
    1,0,0,0,529,530,1,0,0,0,530,55,1,0,0,0,531,529,1,0,0,0,532,541,3,72,
    36,0,533,541,3,78,39,0,534,541,3,88,44,0,535,541,3,90,45,0,536,541,3,
    92,46,0,537,541,3,66,33,0,538,541,3,58,29,0,539,541,3,68,34,0,540,532,
    1,0,0,0,540,533,1,0,0,0,540,534,1,0,0,0,540,535,1,0,0,0,540,536,1,0,
    0,0,540,537,1,0,0,0,540,538,1,0,0,0,540,539,1,0,0,0,541,57,1,0,0,0,542,
    544,3,120,60,0,543,542,1,0,0,0,544,547,1,0,0,0,545,543,1,0,0,0,545,546,
    1,0,0,0,546,551,1,0,0,0,547,545,1,0,0,0,548,550,3,60,30,0,549,548,1,
    0,0,0,550,553,1,0,0,0,551,549,1,0,0,0,551,552,1,0,0,0,552,554,1,0,0,
    0,553,551,1,0,0,0,554,558,5,64,0,0,555,556,3,128,64,0,556,557,5,10,0,
    0,557,559,1,0,0,0,558,555,1,0,0,0,558,559,1,0,0,0,559,561,1,0,0,0,560,
    562,3,62,31,0,561,560,1,0,0,0,561,562,1,0,0,0,562,563,1,0,0,0,563,565,
    3,204,102,0,564,566,3,134,67,0,565,564,1,0,0,0,565,566,1,0,0,0,566,567,
    1,0,0,0,567,572,5,6,0,0,568,570,3,96,48,0,569,571,5,12,0,0,570,569,1,
    0,0,0,570,571,1,0,0,0,571,573,1,0,0,0,572,568,1,0,0,0,572,573,1,0,0,
    0,573,574,1,0,0,0,574,577,5,7,0,0,575,576,5,11,0,0,576,578,3,146,73,
    0,577,575,1,0,0,0,577,578,1,0,0,0,578,580,1,0,0,0,579,581,3,130,65,0,
    580,579,1,0,0,0,580,581,1,0,0,0,581,582,1,0,0,0,582,583,3,64,32,0,583,
    59,1,0,0,0,584,585,5,87,0,0,585,61,1,0,0,0,586,587,5,16,0,0,587,588,
    5,10,0,0,588,63,1,0,0,0,589,590,5,4,0,0,590,591,3,100,50,0,591,592,5,
    5,0,0,592,597,1,0,0,0,593,595,5,1,0,0,594,593,1,0,0,0,594,595,1,0,0,
    0,595,597,1,0,0,0,596,589,1,0,0,0,596,594,1,0,0,0,597,65,1,0,0,0,598,
    600,3,120,60,0,599,598,1,0,0,0,600,603,1,0,0,0,601,599,1,0,0,0,601,602,
    1,0,0,0,602,604,1,0,0,0,603,601,1,0,0,0,604,605,5,68,0,0,605,607,3,204,
    102,0,606,608,3,134,67,0,607,606,1,0,0,0,607,608,1,0,0,0,608,609,1,0,
    0,0,609,614,5,6,0,0,610,612,3,96,48,0,611,613,5,12,0,0,612,611,1,0,0,
    0,612,613,1,0,0,0,613,615,1,0,0,0,614,610,1,0,0,0,614,615,1,0,0,0,615,
    616,1,0,0,0,616,618,5,7,0,0,617,619,3,130,65,0,618,617,1,0,0,0,618,619,
    1,0,0,0,619,621,1,0,0,0,620,622,3,116,58,0,621,620,1,0,0,0,621,622,1,
    0,0,0,622,67,1,0,0,0,623,625,3,120,60,0,624,623,1,0,0,0,625,628,1,0,
    0,0,626,624,1,0,0,0,626,627,1,0,0,0,627,629,1,0,0,0,628,626,1,0,0,0,
    629,630,3,70,35,0,630,633,3,204,102,0,631,632,5,11,0,0,632,634,3,146,
    73,0,633,631,1,0,0,0,633,634,1,0,0,0,634,637,1,0,0,0,635,636,5,2,0,0,
    636,638,3,178,89,0,637,635,1,0,0,0,637,638,1,0,0,0,638,639,1,0,0,0,639,
    640,5,1,0,0,640,69,1,0,0,0,641,644,5,57,0,0,642,644,5,58,0,0,643,641,
    1,0,0,0,643,642,1,0,0,0,644,71,1,0,0,0,645,646,3,74,37,0,646,647,3,76,
    38,0,647,648,5,1,0,0,648,73,1,0,0,0,649,653,5,59,0,0,650,653,5,60,0,
    0,651,653,5,61,0,0,652,649,1,0,0,0,652,650,1,0,0,0,652,651,1,0,0,0,653,
    75,1,0,0,0,654,659,3,204,102,0,655,656,5,12,0,0,656,658,3,204,102,0,
    657,655,1,0,0,0,658,661,1,0,0,0,659,657,1,0,0,0,659,660,1,0,0,0,660,
    77,1,0,0,0,661,659,1,0,0,0,662,663,5,62,0,0,663,664,3,80,40,0,664,665,
    5,13,0,0,665,666,3,204,102,0,666,667,5,78,0,0,667,668,3,82,41,0,668,
    669,5,1,0,0,669,79,1,0,0,0,670,680,3,204,102,0,671,676,5,6,0,0,672,674,
    3,76,38,0,673,675,5,12,0,0,674,673,1,0,0,0,674,675,1,0,0,0,675,677,1,
    0,0,0,676,672,1,0,0,0,676,677,1,0,0,0,677,678,1,0,0,0,678,680,5,7,0,
    0,679,670,1,0,0,0,679,671,1,0,0,0,680,81,1,0,0,0,681,691,3,86,43,0,682,
    687,5,8,0,0,683,685,3,84,42,0,684,686,5,12,0,0,685,684,1,0,0,0,685,686,
    1,0,0,0,686,688,1,0,0,0,687,683,1,0,0,0,687,688,1,0,0,0,688,689,1,0,
    0,0,689,691,5,9,0,0,690,681,1,0,0,0,690,682,1,0,0,0,691,83,1,0,0,0,692,
    697,3,86,43,0,693,694,5,12,0,0,694,696,3,86,43,0,695,693,1,0,0,0,696,
    699,1,0,0,0,697,695,1,0,0,0,697,698,1,0,0,0,698,85,1,0,0,0,699,697,1,
    0,0,0,700,712,3,204,102,0,701,702,3,204,102,0,702,707,5,6,0,0,703,705,
    3,142,71,0,704,706,5,12,0,0,705,704,1,0,0,0,705,706,1,0,0,0,706,708,
    1,0,0,0,707,703,1,0,0,0,707,708,1,0,0,0,708,709,1,0,0,0,709,710,5,7,
    0,0,710,712,1,0,0,0,711,700,1,0,0,0,711,701,1,0,0,0,712,87,1,0,0,0,713,
    715,3,120,60,0,714,713,1,0,0,0,715,718,1,0,0,0,716,714,1,0,0,0,716,717,
    1,0,0,0,717,719,1,0,0,0,718,716,1,0,0,0,719,721,5,65,0,0,720,722,3,62,
    31,0,721,720,1,0,0,0,721,722,1,0,0,0,722,724,1,0,0,0,723,725,3,204,102,
    0,724,723,1,0,0,0,724,725,1,0,0,0,725,726,1,0,0,0,726,731,5,6,0,0,727,
    729,3,96,48,0,728,730,5,12,0,0,729,728,1,0,0,0,729,730,1,0,0,0,730,732,
    1,0,0,0,731,727,1,0,0,0,731,732,1,0,0,0,732,733,1,0,0,0,733,736,5,7,
    0,0,734,735,5,11,0,0,735,737,3,146,73,0,736,734,1,0,0,0,736,737,1,0,
    0,0,737,738,1,0,0,0,738,739,3,64,32,0,739,89,1,0,0,0,740,742,3,120,60,
    0,741,740,1,0,0,0,742,745,1,0,0,0,743,741,1,0,0,0,743,744,1,0,0,0,744,
    746,1,0,0,0,745,743,1,0,0,0,746,748,5,66,0,0,747,749,3,62,31,0,748,747,
    1,0,0,0,748,749,1,0,0,0,749,751,1,0,0,0,750,752,3,204,102,0,751,750,
    1,0,0,0,751,752,1,0,0,0,752,753,1,0,0,0,753,758,5,6,0,0,754,756,3,96,
    48,0,755,757,5,12,0,0,756,755,1,0,0,0,756,757,1,0,0,0,757,759,1,0,0,
    0,758,754,1,0,0,0,758,759,1,0,0,0,759,760,1,0,0,0,760,763,5,7,0,0,761,
    762,5,11,0,0,762,764,3,146,73,0,763,761,1,0,0,0,763,764,1,0,0,0,764,
    765,1,0,0,0,765,766,3,64,32,0,766,91,1,0,0,0,767,769,3,120,60,0,768,
    767,1,0,0,0,769,772,1,0,0,0,770,768,1,0,0,0,770,771,1,0,0,0,771,776,
    1,0,0,0,772,770,1,0,0,0,773,775,3,94,47,0,774,773,1,0,0,0,775,778,1,
    0,0,0,776,774,1,0,0,0,776,777,1,0,0,0,777,779,1,0,0,0,778,776,1,0,0,
    0,779,781,5,67,0,0,780,782,3,62,31,0,781,780,1,0,0,0,781,782,1,0,0,0,
    782,783,1,0,0,0,783,785,3,204,102,0,784,786,3,134,67,0,785,784,1,0,0,
    0,785,786,1,0,0,0,786,787,1,0,0,0,787,792,5,6,0,0,788,790,3,96,48,0,
    789,791,5,12,0,0,790,789,1,0,0,0,790,791,1,0,0,0,791,793,1,0,0,0,792,
    788,1,0,0,0,792,793,1,0,0,0,793,794,1,0,0,0,794,797,5,7,0,0,795,796,
    5,11,0,0,796,798,3,146,73,0,797,795,1,0,0,0,797,798,1,0,0,0,798,800,
    1,0,0,0,799,801,3,130,65,0,800,799,1,0,0,0,800,801,1,0,0,0,801,802,1,
    0,0,0,802,803,3,64,32,0,803,93,1,0,0,0,804,805,5,88,0,0,805,95,1,0,0,
    0,806,811,3,98,49,0,807,808,5,12,0,0,808,810,3,98,49,0,809,807,1,0,0,
    0,810,813,1,0,0,0,811,809,1,0,0,0,811,812,1,0,0,0,812,97,1,0,0,0,813,
    811,1,0,0,0,814,816,3,120,60,0,815,814,1,0,0,0,816,819,1,0,0,0,817,815,
    1,0,0,0,817,818,1,0,0,0,818,820,1,0,0,0,819,817,1,0,0,0,820,821,3,204,
    102,0,821,822,5,11,0,0,822,823,3,146,73,0,823,99,1,0,0,0,824,826,3,102,
    51,0,825,824,1,0,0,0,826,829,1,0,0,0,827,825,1,0,0,0,827,828,1,0,0,0,
    828,833,1,0,0,0,829,827,1,0,0,0,830,832,3,160,80,0,831,830,1,0,0,0,832,
    835,1,0,0,0,833,831,1,0,0,0,833,834,1,0,0,0,834,101,1,0,0,0,835,833,
    1,0,0,0,836,840,3,104,52,0,837,840,3,106,53,0,838,840,3,108,54,0,839,
    836,1,0,0,0,839,837,1,0,0,0,839,838,1,0,0,0,840,103,1,0,0,0,841,845,
    5,70,0,0,842,843,3,204,102,0,843,844,5,11,0,0,844,846,1,0,0,0,845,842,
    1,0,0,0,845,846,1,0,0,0,846,847,1,0,0,0,847,848,3,110,55,0,848,105,1,
    0,0,0,849,853,5,71,0,0,850,851,3,204,102,0,851,852,5,11,0,0,852,854,
    1,0,0,0,853,850,1,0,0,0,853,854,1,0,0,0,854,855,1,0,0,0,855,856,3,110,
    55,0,856,107,1,0,0,0,857,861,5,72,0,0,858,859,3,204,102,0,859,860,5,
    11,0,0,860,862,1,0,0,0,861,858,1,0,0,0,861,862,1,0,0,0,862,863,1,0,0,
    0,863,864,3,178,89,0,864,865,5,1,0,0,865,109,1,0,0,0,866,872,3,116,58,
    0,867,872,3,118,59,0,868,869,3,178,89,0,869,870,5,1,0,0,870,872,1,0,
    0,0,871,866,1,0,0,0,871,867,1,0,0,0,871,868,1,0,0,0,872,111,1,0,0,0,
    873,876,3,116,58,0,874,876,3,178,89,0,875,873,1,0,0,0,875,874,1,0,0,
    0,876,113,1,0,0,0,877,888,3,116,58,0,878,879,3,204,102,0,879,880,5,11,
    0,0,880,881,3,114,57,0,881,888,1,0,0,0,882,888,3,68,34,0,883,888,3,118,
    59,0,884,885,3,178,89,0,885,886,5,1,0,0,886,888,1,0,0,0,887,877,1,0,
    0,0,887,878,1,0,0,0,887,882,1,0,0,0,887,883,1,0,0,0,887,884,1,0,0,0,
    888,115,1,0,0,0,889,893,5,4,0,0,890,892,3,114,57,0,891,890,1,0,0,0,892,
    895,1,0,0,0,893,891,1,0,0,0,893,894,1,0,0,0,894,896,1,0,0,0,895,893,
    1,0,0,0,896,897,5,5,0,0,897,117,1,0,0,0,898,899,5,76,0,0,899,900,5,6,
    0,0,900,901,3,178,89,0,901,902,5,7,0,0,902,905,3,114,57,0,903,904,5,
    77,0,0,904,906,3,114,57,0,905,903,1,0,0,0,905,906,1,0,0,0,906,119,1,
    0,0,0,907,908,5,93,0,0,908,917,3,204,102,0,909,914,5,6,0,0,910,912,3,
    122,61,0,911,913,5,12,0,0,912,911,1,0,0,0,912,913,1,0,0,0,913,915,1,
    0,0,0,914,910,1,0,0,0,914,915,1,0,0,0,915,916,1,0,0,0,916,918,5,7,0,
    0,917,909,1,0,0,0,917,918,1,0,0,0,918,121,1,0,0,0,919,924,3,124,62,0,
    920,921,5,12,0,0,921,923,3,124,62,0,922,920,1,0,0,0,923,926,1,0,0,0,
    924,922,1,0,0,0,924,925,1,0,0,0,925,123,1,0,0,0,926,924,1,0,0,0,927,
    928,3,204,102,0,928,929,5,2,0,0,929,931,1,0,0,0,930,927,1,0,0,0,930,
    931,1,0,0,0,931,932,1,0,0,0,932,933,3,178,89,0,933,125,1,0,0,0,934,936,
    3,128,64,0,935,937,3,134,67,0,936,935,1,0,0,0,936,937,1,0,0,0,937,127,
    1,0,0,0,938,943,3,204,102,0,939,940,5,10,0,0,940,942,3,204,102,0,941,
    939,1,0,0,0,942,945,1,0,0,0,943,941,1,0,0,0,943,944,1,0,0,0,944,129,
    1,0,0,0,945,943,1,0,0,0,946,947,5,84,0,0,947,952,3,132,66,0,948,949,
    5,12,0,0,949,951,3,132,66,0,950,948,1,0,0,0,951,954,1,0,0,0,952,950,
    1,0,0,0,952,953,1,0,0,0,953,956,1,0,0,0,954,952,1,0,0,0,955,957,5,12,
    0,0,956,955,1,0,0,0,956,957,1,0,0,0,957,131,1,0,0,0,958,959,3,204,102,
    0,959,960,5,11,0,0,960,961,3,146,73,0,961,133,1,0,0,0,962,967,5,14,0,
    0,963,965,3,136,68,0,964,966,5,12,0,0,965,964,1,0,0,0,965,966,1,0,0,
    0,966,968,1,0,0,0,967,963,1,0,0,0,967,968,1,0,0,0,968,969,1,0,0,0,969,
    970,5,15,0,0,970,135,1,0,0,0,971,976,3,138,69,0,972,973,5,12,0,0,973,
    975,3,138,69,0,974,972,1,0,0,0,975,978,1,0,0,0,976,974,1,0,0,0,976,977,
    1,0,0,0,977,137,1,0,0,0,978,976,1,0,0,0,979,981,3,140,70,0,980,979,1,
    0,0,0,980,981,1,0,0,0,981,982,1,0,0,0,982,983,3,204,102,0,983,139,1,
    0,0,0,984,989,5,83,0,0,985,989,5,82,0,0,986,987,5,82,0,0,987,989,5,83,
    0,0,988,984,1,0,0,0,988,985,1,0,0,0,988,986,1,0,0,0,989,141,1,0,0,0,
    990,995,3,146,73,0,991,992,5,12,0,0,992,994,3,146,73,0,993,991,1,0,0,
    0,994,997,1,0,0,0,995,993,1,0,0,0,995,996,1,0,0,0,996,143,1,0,0,0,997,
    995,1,0,0,0,998,999,5,6,0,0,999,1000,3,146,73,0,1000,1001,5,7,0,0,1001,
    1006,1,0,0,0,1002,1006,3,190,95,0,1003,1006,3,148,74,0,1004,1006,3,150,
    75,0,1005,998,1,0,0,0,1005,1002,1,0,0,0,1005,1003,1,0,0,0,1005,1004,
    1,0,0,0,1006,145,1,0,0,0,1007,1008,6,73,-1,0,1008,1009,3,144,72,0,1009,
    1018,1,0,0,0,1010,1011,10,2,0,0,1011,1012,5,30,0,0,1012,1017,3,146,73,
    3,1013,1014,10,1,0,0,1014,1015,5,32,0,0,1015,1017,3,146,73,2,1016,1010,
    1,0,0,0,1016,1013,1,0,0,0,1017,1020,1,0,0,0,1018,1016,1,0,0,0,1018,1019,
    1,0,0,0,1019,147,1,0,0,0,1020,1018,1,0,0,0,1021,1023,3,128,64,0,1022,
    1024,3,152,76,0,1023,1022,1,0,0,0,1023,1024,1,0,0,0,1024,149,1,0,0,0,
    1025,1026,5,16,0,0,1026,1027,3,144,72,0,1027,151,1,0,0,0,1028,1033,5,
    14,0,0,1029,1031,3,154,77,0,1030,1032,5,12,0,0,1031,1030,1,0,0,0,1031,
    1032,1,0,0,0,1032,1034,1,0,0,0,1033,1029,1,0,0,0,1033,1034,1,0,0,0,1034,
    1035,1,0,0,0,1035,1036,5,15,0,0,1036,153,1,0,0,0,1037,1042,3,156,78,
    0,1038,1039,5,12,0,0,1039,1041,3,156,78,0,1040,1038,1,0,0,0,1041,1044,
    1,0,0,0,1042,1040,1,0,0,0,1042,1043,1,0,0,0,1043,155,1,0,0,0,1044,1042,
    1,0,0,0,1045,1047,3,140,70,0,1046,1045,1,0,0,0,1046,1047,1,0,0,0,1047,
    1048,1,0,0,0,1048,1051,3,146,73,0,1049,1051,5,90,0,0,1050,1046,1,0,0,
    0,1050,1049,1,0,0,0,1051,157,1,0,0,0,1052,1062,3,160,80,0,1053,1057,
    5,4,0,0,1054,1056,3,160,80,0,1055,1054,1,0,0,0,1056,1059,1,0,0,0,1057,
    1055,1,0,0,0,1057,1058,1,0,0,0,1058,1060,1,0,0,0,1059,1057,1,0,0,0,1060,
    1062,5,5,0,0,1061,1052,1,0,0,0,1061,1053,1,0,0,0,1062,159,1,0,0,0,1063,
    1071,3,68,34,0,1064,1071,3,162,81,0,1065,1071,3,164,82,0,1066,1071,3,
    168,84,0,1067,1068,3,178,89,0,1068,1069,5,1,0,0,1069,1071,1,0,0,0,1070,
    1063,1,0,0,0,1070,1064,1,0,0,0,1070,1065,1,0,0,0,1070,1066,1,0,0,0,1070,
    1067,1,0,0,0,1071,161,1,0,0,0,1072,1073,5,76,0,0,1073,1074,5,6,0,0,1074,
    1075,3,178,89,0,1075,1076,5,7,0,0,1076,1079,3,158,79,0,1077,1078,5,77,
    0,0,1078,1080,3,158,79,0,1079,1077,1,0,0,0,1079,1080,1,0,0,0,1080,163,
    1,0,0,0,1081,1082,3,166,83,0,1082,1083,3,170,85,0,1083,1084,3,178,89,
    0,1084,1085,5,1,0,0,1085,165,1,0,0,0,1086,1097,3,204,102,0,1087,1088,
    3,178,89,0,1088,1089,5,10,0,0,1089,1090,3,204,102,0,1090,1097,1,0,0,
    0,1091,1092,3,178,89,0,1092,1093,5,8,0,0,1093,1094,3,178,89,0,1094,1095,
    5,9,0,0,1095,1097,1,0,0,0,1096,1086,1,0,0,0,1096,1087,1,0,0,0,1096,1091,
    1,0,0,0,1097,167,1,0,0,0,1098,1099,5,91,0,0,1099,1100,5,1,0,0,1100,169,
    1,0,0,0,1101,1113,5,2,0,0,1102,1113,5,21,0,0,1103,1113,5,22,0,0,1104,
    1113,5,23,0,0,1105,1113,5,24,0,0,1106,1113,5,25,0,0,1107,1113,5,36,0,
    0,1108,1113,5,37,0,0,1109,1113,5,38,0,0,1110,1113,5,40,0,0,1111,1113,
    5,39,0,0,1112,1101,1,0,0,0,1112,1102,1,0,0,0,1112,1103,1,0,0,0,1112,
    1104,1,0,0,0,1112,1105,1,0,0,0,1112,1106,1,0,0,0,1112,1107,1,0,0,0,1112,
    1108,1,0,0,0,1112,1109,1,0,0,0,1112,1110,1,0,0,0,1112,1111,1,0,0,0,1113,
    171,1,0,0,0,1114,1119,3,178,89,0,1115,1116,5,12,0,0,1116,1118,3,178,
    89,0,1117,1115,1,0,0,0,1118,1121,1,0,0,0,1119,1117,1,0,0,0,1119,1120,
    1,0,0,0,1120,173,1,0,0,0,1121,1119,1,0,0,0,1122,1123,5,6,0,0,1123,1124,
    3,174,87,0,1124,1125,5,7,0,0,1125,1132,1,0,0,0,1126,1132,3,190,95,0,
    1127,1132,3,176,88,0,1128,1132,3,192,96,0,1129,1132,3,194,97,0,1130,
    1132,3,204,102,0,1131,1122,1,0,0,0,1131,1126,1,0,0,0,1131,1127,1,0,0,
    0,1131,1128,1,0,0,0,1131,1129,1,0,0,0,1131,1130,1,0,0,0,1132,175,1,0,
    0,0,1133,1134,3,34,17,0,1134,1135,5,92,0,0,1135,1140,1,0,0,0,1136,1137,
    3,34,17,0,1137,1138,5,94,0,0,1138,1140,1,0,0,0,1139,1133,1,0,0,0,1139,
    1136,1,0,0,0,1140,177,1,0,0,0,1141,1142,6,89,-1,0,1142,1143,5,6,0,0,
    1143,1144,3,178,89,0,1144,1145,5,7,0,0,1145,1169,1,0,0,0,1146,1169,3,
    190,95,0,1147,1169,3,192,96,0,1148,1169,3,194,97,0,1149,1151,3,204,102,
    0,1150,1152,3,152,76,0,1151,1150,1,0,0,0,1151,1152,1,0,0,0,1152,1153,
    1,0,0,0,1153,1158,5,6,0,0,1154,1156,3,172,86,0,1155,1157,5,12,0,0,1156,
    1155,1,0,0,0,1156,1157,1,0,0,0,1157,1159,1,0,0,0,1158,1154,1,0,0,0,1158,
    1159,1,0,0,0,1159,1160,1,0,0,0,1160,1161,5,7,0,0,1161,1169,1,0,0,0,1162,
    1169,3,196,98,0,1163,1169,3,198,99,0,1164,1169,3,204,102,0,1165,1166,
    3,180,90,0,1166,1167,3,178,89,13,1167,1169,1,0,0,0,1168,1141,1,0,0,0,
    1168,1146,1,0,0,0,1168,1147,1,0,0,0,1168,1148,1,0,0,0,1168,1149,1,0,
    0,0,1168,1162,1,0,0,0,1168,1163,1,0,0,0,1168,1164,1,0,0,0,1168,1165,
    1,0,0,0,1169,1246,1,0,0,0,1170,1171,10,9,0,0,1171,1172,3,182,91,0,1172,
    1173,3,178,89,10,1173,1245,1,0,0,0,1174,1175,10,8,0,0,1175,1176,3,184,
    92,0,1176,1177,3,178,89,9,1177,1245,1,0,0,0,1178,1179,10,7,0,0,1179,
    1180,3,186,93,0,1180,1181,3,178,89,8,1181,1245,1,0,0,0,1182,1183,10,
    6,0,0,1183,1184,5,30,0,0,1184,1245,3,178,89,7,1185,1186,10,5,0,0,1186,
    1187,5,34,0,0,1187,1245,3,178,89,6,1188,1189,10,4,0,0,1189,1190,5,32,
    0,0,1190,1245,3,178,89,5,1191,1192,10,3,0,0,1192,1193,3,188,94,0,1193,
    1194,3,178,89,4,1194,1245,1,0,0,0,1195,1196,10,2,0,0,1196,1197,5,31,
    0,0,1197,1245,3,178,89,3,1198,1199,10,1,0,0,1199,1200,5,33,0,0,1200,
    1245,3,178,89,2,1201,1202,10,18,0,0,1202,1245,5,41,0,0,1203,1204,10,
    17,0,0,1204,1205,5,10,0,0,1205,1207,3,204,102,0,1206,1208,3,152,76,0,
    1207,1206,1,0,0,0,1207,1208,1,0,0,0,1208,1209,1,0,0,0,1209,1214,5,6,
    0,0,1210,1212,3,172,86,0,1211,1213,5,12,0,0,1212,1211,1,0,0,0,1212,1213,
    1,0,0,0,1213,1215,1,0,0,0,1214,1210,1,0,0,0,1214,1215,1,0,0,0,1215,1216,
    1,0,0,0,1216,1217,5,7,0,0,1217,1245,1,0,0,0,1218,1219,10,16,0,0,1219,
    1220,5,10,0,0,1220,1245,3,204,102,0,1221,1222,10,15,0,0,1222,1223,5,
    10,0,0,1223,1245,5,16,0,0,1224,1225,10,14,0,0,1225,1226,5,8,0,0,1226,
    1227,3,178,89,0,1227,1228,5,9,0,0,1228,1245,1,0,0,0,1229,1231,10,12,
    0,0,1230,1232,5,26,0,0,1231,1230,1,0,0,0,1231,1232,1,0,0,0,1232,1233,
    1,0,0,0,1233,1234,5,89,0,0,1234,1245,3,204,102,0,1235,1237,10,11,0,0,
    1236,1238,5,26,0,0,1237,1236,1,0,0,0,1237,1238,1,0,0,0,1238,1239,1,0,
    0,0,1239,1240,5,79,0,0,1240,1245,3,146,73,0,1241,1242,10,10,0,0,1242,
    1243,5,80,0,0,1243,1245,3,146,73,0,1244,1170,1,0,0,0,1244,1174,1,0,0,
    0,1244,1178,1,0,0,0,1244,1182,1,0,0,0,1244,1185,1,0,0,0,1244,1188,1,
    0,0,0,1244,1191,1,0,0,0,1244,1195,1,0,0,0,1244,1198,1,0,0,0,1244,1201,
    1,0,0,0,1244,1203,1,0,0,0,1244,1218,1,0,0,0,1244,1221,1,0,0,0,1244,1224,
    1,0,0,0,1244,1229,1,0,0,0,1244,1235,1,0,0,0,1244,1241,1,0,0,0,1245,1248,
    1,0,0,0,1246,1244,1,0,0,0,1246,1247,1,0,0,0,1247,179,1,0,0,0,1248,1246,
    1,0,0,0,1249,1254,5,19,0,0,1250,1254,5,20,0,0,1251,1254,5,35,0,0,1252,
    1254,5,26,0,0,1253,1249,1,0,0,0,1253,1250,1,0,0,0,1253,1251,1,0,0,0,
    1253,1252,1,0,0,0,1254,181,1,0,0,0,1255,1259,5,16,0,0,1256,1259,5,17,
    0,0,1257,1259,5,18,0,0,1258,1255,1,0,0,0,1258,1256,1,0,0,0,1258,1257,
    1,0,0,0,1259,183,1,0,0,0,1260,1263,5,19,0,0,1261,1263,5,20,0,0,1262,
    1260,1,0,0,0,1262,1261,1,0,0,0,1263,185,1,0,0,0,1264,1265,5,14,0,0,1265,
    1266,5,14,0,0,1266,1275,5,14,0,0,1267,1268,5,15,0,0,1268,1269,5,15,0,
    0,1269,1275,5,15,0,0,1270,1271,5,14,0,0,1271,1275,5,14,0,0,1272,1273,
    5,15,0,0,1273,1275,5,15,0,0,1274,1264,1,0,0,0,1274,1267,1,0,0,0,1274,
    1270,1,0,0,0,1274,1272,1,0,0,0,1275,187,1,0,0,0,1276,1287,5,28,0,0,1277,
    1287,5,29,0,0,1278,1287,5,14,0,0,1279,1287,5,15,0,0,1280,1287,5,3,0,
    0,1281,1287,5,27,0,0,1282,1284,5,26,0,0,1283,1282,1,0,0,0,1283,1284,
    1,0,0,0,1284,1285,1,0,0,0,1285,1287,5,82,0,0,1286,1276,1,0,0,0,1286,
    1277,1,0,0,0,1286,1278,1,0,0,0,1286,1279,1,0,0,0,1286,1280,1,0,0,0,1286,
    1281,1,0,0,0,1286,1283,1,0,0,0,1287,189,1,0,0,0,1288,1296,5,92,0,0,1289,
    1296,5,94,0,0,1290,1296,5,96,0,0,1291,1296,5,97,0,0,1292,1296,5,73,0,
    0,1293,1296,5,74,0,0,1294,1296,5,81,0,0,1295,1288,1,0,0,0,1295,1289,
    1,0,0,0,1295,1290,1,0,0,0,1295,1291,1,0,0,0,1295,1292,1,0,0,0,1295,1293,
    1,0,0,0,1295,1294,1,0,0,0,1296,191,1,0,0,0,1297,1302,5,8,0,0,1298,1300,
    3,172,86,0,1299,1301,5,12,0,0,1300,1299,1,0,0,0,1300,1301,1,0,0,0,1301,
    1303,1,0,0,0,1302,1298,1,0,0,0,1302,1303,1,0,0,0,1303,1304,1,0,0,0,1304,
    1305,5,9,0,0,1305,193,1,0,0,0,1306,1311,5,4,0,0,1307,1309,3,172,86,0,
    1308,1310,5,12,0,0,1309,1308,1,0,0,0,1309,1310,1,0,0,0,1310,1312,1,0,
    0,0,1311,1307,1,0,0,0,1311,1312,1,0,0,0,1312,1313,1,0,0,0,1313,1314,
    5,5,0,0,1314,195,1,0,0,0,1315,1316,5,69,0,0,1316,1318,3,204,102,0,1317,
    1319,3,152,76,0,1318,1317,1,0,0,0,1318,1319,1,0,0,0,1319,1320,1,0,0,
    0,1320,1325,5,6,0,0,1321,1323,3,172,86,0,1322,1324,5,12,0,0,1323,1322,
    1,0,0,0,1323,1324,1,0,0,0,1324,1326,1,0,0,0,1325,1321,1,0,0,0,1325,1326,
    1,0,0,0,1326,1327,1,0,0,0,1327,1328,5,7,0,0,1328,197,1,0,0,0,1329,1330,
    5,63,0,0,1330,1332,3,128,64,0,1331,1333,3,152,76,0,1332,1331,1,0,0,0,
    1332,1333,1,0,0,0,1333,1334,1,0,0,0,1334,1339,5,6,0,0,1335,1337,3,200,
    100,0,1336,1338,5,12,0,0,1337,1336,1,0,0,0,1337,1338,1,0,0,0,1338,1340,
    1,0,0,0,1339,1335,1,0,0,0,1339,1340,1,0,0,0,1340,1341,1,0,0,0,1341,1342,
    5,7,0,0,1342,199,1,0,0,0,1343,1348,3,202,101,0,1344,1345,5,12,0,0,1345,
    1347,3,202,101,0,1346,1344,1,0,0,0,1347,1350,1,0,0,0,1348,1346,1,0,0,
    0,1348,1349,1,0,0,0,1349,201,1,0,0,0,1350,1348,1,0,0,0,1351,1352,5,60,
    0,0,1352,1353,5,2,0,0,1353,1359,3,204,102,0,1354,1355,3,204,102,0,1355,
    1356,5,2,0,0,1356,1357,3,178,89,0,1357,1359,1,0,0,0,1358,1351,1,0,0,
    0,1358,1354,1,0,0,0,1359,203,1,0,0,0,1360,1361,7,0,0,0,1361,205,1,0,
    0,0,179,207,212,224,228,232,249,261,268,276,290,294,304,316,322,325,
    331,335,339,344,350,355,364,375,381,388,390,400,408,413,420,425,427,
    432,435,444,450,460,465,471,473,476,482,486,490,496,506,512,521,529,
    540,545,551,558,561,565,570,572,577,580,594,596,601,607,612,614,618,
    621,626,633,637,643,652,659,674,676,679,685,687,690,697,705,707,711,
    716,721,724,729,731,736,743,748,751,756,758,763,770,776,781,785,790,
    792,797,800,811,817,827,833,839,845,853,861,871,875,887,893,905,912,
    914,917,924,930,936,943,952,956,965,967,976,980,988,995,1005,1016,1018,
    1023,1031,1033,1042,1046,1050,1057,1061,1070,1079,1096,1112,1119,1131,
    1139,1151,1156,1158,1168,1207,1212,1214,1231,1237,1244,1246,1253,1258,
    1262,1274,1283,1286,1295,1300,1302,1309,1311,1318,1323,1325,1332,1337,
    1339,1348,1358
];

