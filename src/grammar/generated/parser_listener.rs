#![allow(nonstandard_style)]
// Generated from ./LibSLParser.g4 by ANTLR 4.13.2
use antlr_rust::tree::ParseTreeListener;
use super::libslparser::*;

pub trait LibSLParserListener<'input> : ParseTreeListener<'input,LibSLParserContextType>{
/**
 * Enter a parse tree produced by {@link LibSLParser#file}.
 * @param ctx the parse tree
 */
fn enter_file(&mut self, _ctx: &FileContext<'input>) { }
/**
 * Exit a parse tree produced by {@link LibSLParser#file}.
 * @param ctx the parse tree
 */
fn exit_file(&mut self, _ctx: &FileContext<'input>) { }
/**
 * Enter a parse tree produced by {@link LibSLParser#header}.
 * @param ctx the parse tree
 */
fn enter_header(&mut self, _ctx: &HeaderContext<'input>) { }
/**
 * Exit a parse tree produced by {@link LibSLParser#header}.
 * @param ctx the parse tree
 */
fn exit_header(&mut self, _ctx: &HeaderContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code GlobalDeclImport}
 * labeled alternative in {@link LibSLParser#globalDecl}.
 * @param ctx the parse tree
 */
fn enter_GlobalDeclImport(&mut self, _ctx: &GlobalDeclImportContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code GlobalDeclImport}
 * labeled alternative in {@link LibSLParser#globalDecl}.
 * @param ctx the parse tree
 */
fn exit_GlobalDeclImport(&mut self, _ctx: &GlobalDeclImportContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code GlobalDeclInclude}
 * labeled alternative in {@link LibSLParser#globalDecl}.
 * @param ctx the parse tree
 */
fn enter_GlobalDeclInclude(&mut self, _ctx: &GlobalDeclIncludeContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code GlobalDeclInclude}
 * labeled alternative in {@link LibSLParser#globalDecl}.
 * @param ctx the parse tree
 */
fn exit_GlobalDeclInclude(&mut self, _ctx: &GlobalDeclIncludeContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code GlobalDeclSemanticTypeSection}
 * labeled alternative in {@link LibSLParser#globalDecl}.
 * @param ctx the parse tree
 */
fn enter_GlobalDeclSemanticTypeSection(&mut self, _ctx: &GlobalDeclSemanticTypeSectionContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code GlobalDeclSemanticTypeSection}
 * labeled alternative in {@link LibSLParser#globalDecl}.
 * @param ctx the parse tree
 */
fn exit_GlobalDeclSemanticTypeSection(&mut self, _ctx: &GlobalDeclSemanticTypeSectionContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code GlobalDeclTypeAlias}
 * labeled alternative in {@link LibSLParser#globalDecl}.
 * @param ctx the parse tree
 */
fn enter_GlobalDeclTypeAlias(&mut self, _ctx: &GlobalDeclTypeAliasContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code GlobalDeclTypeAlias}
 * labeled alternative in {@link LibSLParser#globalDecl}.
 * @param ctx the parse tree
 */
fn exit_GlobalDeclTypeAlias(&mut self, _ctx: &GlobalDeclTypeAliasContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code GlobalDeclStruct}
 * labeled alternative in {@link LibSLParser#globalDecl}.
 * @param ctx the parse tree
 */
fn enter_GlobalDeclStruct(&mut self, _ctx: &GlobalDeclStructContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code GlobalDeclStruct}
 * labeled alternative in {@link LibSLParser#globalDecl}.
 * @param ctx the parse tree
 */
fn exit_GlobalDeclStruct(&mut self, _ctx: &GlobalDeclStructContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code GlobalDeclEnum}
 * labeled alternative in {@link LibSLParser#globalDecl}.
 * @param ctx the parse tree
 */
fn enter_GlobalDeclEnum(&mut self, _ctx: &GlobalDeclEnumContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code GlobalDeclEnum}
 * labeled alternative in {@link LibSLParser#globalDecl}.
 * @param ctx the parse tree
 */
fn exit_GlobalDeclEnum(&mut self, _ctx: &GlobalDeclEnumContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code GlobalDeclAnnotation}
 * labeled alternative in {@link LibSLParser#globalDecl}.
 * @param ctx the parse tree
 */
fn enter_GlobalDeclAnnotation(&mut self, _ctx: &GlobalDeclAnnotationContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code GlobalDeclAnnotation}
 * labeled alternative in {@link LibSLParser#globalDecl}.
 * @param ctx the parse tree
 */
fn exit_GlobalDeclAnnotation(&mut self, _ctx: &GlobalDeclAnnotationContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code GlobalDeclAction}
 * labeled alternative in {@link LibSLParser#globalDecl}.
 * @param ctx the parse tree
 */
fn enter_GlobalDeclAction(&mut self, _ctx: &GlobalDeclActionContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code GlobalDeclAction}
 * labeled alternative in {@link LibSLParser#globalDecl}.
 * @param ctx the parse tree
 */
fn exit_GlobalDeclAction(&mut self, _ctx: &GlobalDeclActionContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code GlobalDeclAutomaton}
 * labeled alternative in {@link LibSLParser#globalDecl}.
 * @param ctx the parse tree
 */
fn enter_GlobalDeclAutomaton(&mut self, _ctx: &GlobalDeclAutomatonContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code GlobalDeclAutomaton}
 * labeled alternative in {@link LibSLParser#globalDecl}.
 * @param ctx the parse tree
 */
fn exit_GlobalDeclAutomaton(&mut self, _ctx: &GlobalDeclAutomatonContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code GlobalDeclFunction}
 * labeled alternative in {@link LibSLParser#globalDecl}.
 * @param ctx the parse tree
 */
fn enter_GlobalDeclFunction(&mut self, _ctx: &GlobalDeclFunctionContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code GlobalDeclFunction}
 * labeled alternative in {@link LibSLParser#globalDecl}.
 * @param ctx the parse tree
 */
fn exit_GlobalDeclFunction(&mut self, _ctx: &GlobalDeclFunctionContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code GlobalDeclProc}
 * labeled alternative in {@link LibSLParser#globalDecl}.
 * @param ctx the parse tree
 */
fn enter_GlobalDeclProc(&mut self, _ctx: &GlobalDeclProcContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code GlobalDeclProc}
 * labeled alternative in {@link LibSLParser#globalDecl}.
 * @param ctx the parse tree
 */
fn exit_GlobalDeclProc(&mut self, _ctx: &GlobalDeclProcContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code GlobalDeclVariable}
 * labeled alternative in {@link LibSLParser#globalDecl}.
 * @param ctx the parse tree
 */
fn enter_GlobalDeclVariable(&mut self, _ctx: &GlobalDeclVariableContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code GlobalDeclVariable}
 * labeled alternative in {@link LibSLParser#globalDecl}.
 * @param ctx the parse tree
 */
fn exit_GlobalDeclVariable(&mut self, _ctx: &GlobalDeclVariableContext<'input>) { }
/**
 * Enter a parse tree produced by {@link LibSLParser#importDecl}.
 * @param ctx the parse tree
 */
fn enter_importDecl(&mut self, _ctx: &ImportDeclContext<'input>) { }
/**
 * Exit a parse tree produced by {@link LibSLParser#importDecl}.
 * @param ctx the parse tree
 */
fn exit_importDecl(&mut self, _ctx: &ImportDeclContext<'input>) { }
/**
 * Enter a parse tree produced by {@link LibSLParser#includeDecl}.
 * @param ctx the parse tree
 */
fn enter_includeDecl(&mut self, _ctx: &IncludeDeclContext<'input>) { }
/**
 * Exit a parse tree produced by {@link LibSLParser#includeDecl}.
 * @param ctx the parse tree
 */
fn exit_includeDecl(&mut self, _ctx: &IncludeDeclContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code PathStringLit}
 * labeled alternative in {@link LibSLParser#path}.
 * @param ctx the parse tree
 */
fn enter_PathStringLit(&mut self, _ctx: &PathStringLitContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code PathStringLit}
 * labeled alternative in {@link LibSLParser#path}.
 * @param ctx the parse tree
 */
fn exit_PathStringLit(&mut self, _ctx: &PathStringLitContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code PathBare}
 * labeled alternative in {@link LibSLParser#path}.
 * @param ctx the parse tree
 */
fn enter_PathBare(&mut self, _ctx: &PathBareContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code PathBare}
 * labeled alternative in {@link LibSLParser#path}.
 * @param ctx the parse tree
 */
fn exit_PathBare(&mut self, _ctx: &PathBareContext<'input>) { }
/**
 * Enter a parse tree produced by {@link LibSLParser#semanticTypeSectionDecl}.
 * @param ctx the parse tree
 */
fn enter_semanticTypeSectionDecl(&mut self, _ctx: &SemanticTypeSectionDeclContext<'input>) { }
/**
 * Exit a parse tree produced by {@link LibSLParser#semanticTypeSectionDecl}.
 * @param ctx the parse tree
 */
fn exit_semanticTypeSectionDecl(&mut self, _ctx: &SemanticTypeSectionDeclContext<'input>) { }
/**
 * Enter a parse tree produced by {@link LibSLParser#semanticTypeDecl}.
 * @param ctx the parse tree
 */
fn enter_semanticTypeDecl(&mut self, _ctx: &SemanticTypeDeclContext<'input>) { }
/**
 * Exit a parse tree produced by {@link LibSLParser#semanticTypeDecl}.
 * @param ctx the parse tree
 */
fn exit_semanticTypeDecl(&mut self, _ctx: &SemanticTypeDeclContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code SemanticTypeDefSimple}
 * labeled alternative in {@link LibSLParser#semanticTypeDef}.
 * @param ctx the parse tree
 */
fn enter_SemanticTypeDefSimple(&mut self, _ctx: &SemanticTypeDefSimpleContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code SemanticTypeDefSimple}
 * labeled alternative in {@link LibSLParser#semanticTypeDef}.
 * @param ctx the parse tree
 */
fn exit_SemanticTypeDefSimple(&mut self, _ctx: &SemanticTypeDefSimpleContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code SemanticTypeDefEnum}
 * labeled alternative in {@link LibSLParser#semanticTypeDef}.
 * @param ctx the parse tree
 */
fn enter_SemanticTypeDefEnum(&mut self, _ctx: &SemanticTypeDefEnumContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code SemanticTypeDefEnum}
 * labeled alternative in {@link LibSLParser#semanticTypeDef}.
 * @param ctx the parse tree
 */
fn exit_SemanticTypeDefEnum(&mut self, _ctx: &SemanticTypeDefEnumContext<'input>) { }
/**
 * Enter a parse tree produced by {@link LibSLParser#enumSemanticTypeValue}.
 * @param ctx the parse tree
 */
fn enter_enumSemanticTypeValue(&mut self, _ctx: &EnumSemanticTypeValueContext<'input>) { }
/**
 * Exit a parse tree produced by {@link LibSLParser#enumSemanticTypeValue}.
 * @param ctx the parse tree
 */
fn exit_enumSemanticTypeValue(&mut self, _ctx: &EnumSemanticTypeValueContext<'input>) { }
/**
 * Enter a parse tree produced by {@link LibSLParser#typeAliasDecl}.
 * @param ctx the parse tree
 */
fn enter_typeAliasDecl(&mut self, _ctx: &TypeAliasDeclContext<'input>) { }
/**
 * Exit a parse tree produced by {@link LibSLParser#typeAliasDecl}.
 * @param ctx the parse tree
 */
fn exit_typeAliasDecl(&mut self, _ctx: &TypeAliasDeclContext<'input>) { }
/**
 * Enter a parse tree produced by {@link LibSLParser#structDecl}.
 * @param ctx the parse tree
 */
fn enter_structDecl(&mut self, _ctx: &StructDeclContext<'input>) { }
/**
 * Exit a parse tree produced by {@link LibSLParser#structDecl}.
 * @param ctx the parse tree
 */
fn exit_structDecl(&mut self, _ctx: &StructDeclContext<'input>) { }
/**
 * Enter a parse tree produced by {@link LibSLParser#structTargetType}.
 * @param ctx the parse tree
 */
fn enter_structTargetType(&mut self, _ctx: &StructTargetTypeContext<'input>) { }
/**
 * Exit a parse tree produced by {@link LibSLParser#structTargetType}.
 * @param ctx the parse tree
 */
fn exit_structTargetType(&mut self, _ctx: &StructTargetTypeContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code StructDefDeclVariable}
 * labeled alternative in {@link LibSLParser#structDefDecl}.
 * @param ctx the parse tree
 */
fn enter_StructDefDeclVariable(&mut self, _ctx: &StructDefDeclVariableContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code StructDefDeclVariable}
 * labeled alternative in {@link LibSLParser#structDefDecl}.
 * @param ctx the parse tree
 */
fn exit_StructDefDeclVariable(&mut self, _ctx: &StructDefDeclVariableContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code StructDefDeclFunction}
 * labeled alternative in {@link LibSLParser#structDefDecl}.
 * @param ctx the parse tree
 */
fn enter_StructDefDeclFunction(&mut self, _ctx: &StructDefDeclFunctionContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code StructDefDeclFunction}
 * labeled alternative in {@link LibSLParser#structDefDecl}.
 * @param ctx the parse tree
 */
fn exit_StructDefDeclFunction(&mut self, _ctx: &StructDefDeclFunctionContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code StructDefDeclProc}
 * labeled alternative in {@link LibSLParser#structDefDecl}.
 * @param ctx the parse tree
 */
fn enter_StructDefDeclProc(&mut self, _ctx: &StructDefDeclProcContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code StructDefDeclProc}
 * labeled alternative in {@link LibSLParser#structDefDecl}.
 * @param ctx the parse tree
 */
fn exit_StructDefDeclProc(&mut self, _ctx: &StructDefDeclProcContext<'input>) { }
/**
 * Enter a parse tree produced by {@link LibSLParser#enumDecl}.
 * @param ctx the parse tree
 */
fn enter_enumDecl(&mut self, _ctx: &EnumDeclContext<'input>) { }
/**
 * Exit a parse tree produced by {@link LibSLParser#enumDecl}.
 * @param ctx the parse tree
 */
fn exit_enumDecl(&mut self, _ctx: &EnumDeclContext<'input>) { }
/**
 * Enter a parse tree produced by {@link LibSLParser#enumDeclVariant}.
 * @param ctx the parse tree
 */
fn enter_enumDeclVariant(&mut self, _ctx: &EnumDeclVariantContext<'input>) { }
/**
 * Exit a parse tree produced by {@link LibSLParser#enumDeclVariant}.
 * @param ctx the parse tree
 */
fn exit_enumDeclVariant(&mut self, _ctx: &EnumDeclVariantContext<'input>) { }
/**
 * Enter a parse tree produced by {@link LibSLParser#signedIntLit}.
 * @param ctx the parse tree
 */
fn enter_signedIntLit(&mut self, _ctx: &SignedIntLitContext<'input>) { }
/**
 * Exit a parse tree produced by {@link LibSLParser#signedIntLit}.
 * @param ctx the parse tree
 */
fn exit_signedIntLit(&mut self, _ctx: &SignedIntLitContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code MinusSign}
 * labeled alternative in {@link LibSLParser#sign}.
 * @param ctx the parse tree
 */
fn enter_MinusSign(&mut self, _ctx: &MinusSignContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code MinusSign}
 * labeled alternative in {@link LibSLParser#sign}.
 * @param ctx the parse tree
 */
fn exit_MinusSign(&mut self, _ctx: &MinusSignContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code PlusSign}
 * labeled alternative in {@link LibSLParser#sign}.
 * @param ctx the parse tree
 */
fn enter_PlusSign(&mut self, _ctx: &PlusSignContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code PlusSign}
 * labeled alternative in {@link LibSLParser#sign}.
 * @param ctx the parse tree
 */
fn exit_PlusSign(&mut self, _ctx: &PlusSignContext<'input>) { }
/**
 * Enter a parse tree produced by {@link LibSLParser#annotationDecl}.
 * @param ctx the parse tree
 */
fn enter_annotationDecl(&mut self, _ctx: &AnnotationDeclContext<'input>) { }
/**
 * Exit a parse tree produced by {@link LibSLParser#annotationDecl}.
 * @param ctx the parse tree
 */
fn exit_annotationDecl(&mut self, _ctx: &AnnotationDeclContext<'input>) { }
/**
 * Enter a parse tree produced by {@link LibSLParser#annotationParamList}.
 * @param ctx the parse tree
 */
fn enter_annotationParamList(&mut self, _ctx: &AnnotationParamListContext<'input>) { }
/**
 * Exit a parse tree produced by {@link LibSLParser#annotationParamList}.
 * @param ctx the parse tree
 */
fn exit_annotationParamList(&mut self, _ctx: &AnnotationParamListContext<'input>) { }
/**
 * Enter a parse tree produced by {@link LibSLParser#annotationParam}.
 * @param ctx the parse tree
 */
fn enter_annotationParam(&mut self, _ctx: &AnnotationParamContext<'input>) { }
/**
 * Exit a parse tree produced by {@link LibSLParser#annotationParam}.
 * @param ctx the parse tree
 */
fn exit_annotationParam(&mut self, _ctx: &AnnotationParamContext<'input>) { }
/**
 * Enter a parse tree produced by {@link LibSLParser#actionDecl}.
 * @param ctx the parse tree
 */
fn enter_actionDecl(&mut self, _ctx: &ActionDeclContext<'input>) { }
/**
 * Exit a parse tree produced by {@link LibSLParser#actionDecl}.
 * @param ctx the parse tree
 */
fn exit_actionDecl(&mut self, _ctx: &ActionDeclContext<'input>) { }
/**
 * Enter a parse tree produced by {@link LibSLParser#actionParamList}.
 * @param ctx the parse tree
 */
fn enter_actionParamList(&mut self, _ctx: &ActionParamListContext<'input>) { }
/**
 * Exit a parse tree produced by {@link LibSLParser#actionParamList}.
 * @param ctx the parse tree
 */
fn exit_actionParamList(&mut self, _ctx: &ActionParamListContext<'input>) { }
/**
 * Enter a parse tree produced by {@link LibSLParser#actionParam}.
 * @param ctx the parse tree
 */
fn enter_actionParam(&mut self, _ctx: &ActionParamContext<'input>) { }
/**
 * Exit a parse tree produced by {@link LibSLParser#actionParam}.
 * @param ctx the parse tree
 */
fn exit_actionParam(&mut self, _ctx: &ActionParamContext<'input>) { }
/**
 * Enter a parse tree produced by {@link LibSLParser#automatonDecl}.
 * @param ctx the parse tree
 */
fn enter_automatonDecl(&mut self, _ctx: &AutomatonDeclContext<'input>) { }
/**
 * Exit a parse tree produced by {@link LibSLParser#automatonDecl}.
 * @param ctx the parse tree
 */
fn exit_automatonDecl(&mut self, _ctx: &AutomatonDeclContext<'input>) { }
/**
 * Enter a parse tree produced by {@link LibSLParser#constructorVariableList}.
 * @param ctx the parse tree
 */
fn enter_constructorVariableList(&mut self, _ctx: &ConstructorVariableListContext<'input>) { }
/**
 * Exit a parse tree produced by {@link LibSLParser#constructorVariableList}.
 * @param ctx the parse tree
 */
fn exit_constructorVariableList(&mut self, _ctx: &ConstructorVariableListContext<'input>) { }
/**
 * Enter a parse tree produced by {@link LibSLParser#constructorVariable}.
 * @param ctx the parse tree
 */
fn enter_constructorVariable(&mut self, _ctx: &ConstructorVariableContext<'input>) { }
/**
 * Exit a parse tree produced by {@link LibSLParser#constructorVariable}.
 * @param ctx the parse tree
 */
fn exit_constructorVariable(&mut self, _ctx: &ConstructorVariableContext<'input>) { }
/**
 * Enter a parse tree produced by {@link LibSLParser#implementedConcepts}.
 * @param ctx the parse tree
 */
fn enter_implementedConcepts(&mut self, _ctx: &ImplementedConceptsContext<'input>) { }
/**
 * Exit a parse tree produced by {@link LibSLParser#implementedConcepts}.
 * @param ctx the parse tree
 */
fn exit_implementedConcepts(&mut self, _ctx: &ImplementedConceptsContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code AutomatonDefDeclState}
 * labeled alternative in {@link LibSLParser#automatonDefDecl}.
 * @param ctx the parse tree
 */
fn enter_AutomatonDefDeclState(&mut self, _ctx: &AutomatonDefDeclStateContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code AutomatonDefDeclState}
 * labeled alternative in {@link LibSLParser#automatonDefDecl}.
 * @param ctx the parse tree
 */
fn exit_AutomatonDefDeclState(&mut self, _ctx: &AutomatonDefDeclStateContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code AutomatonDefDeclShift}
 * labeled alternative in {@link LibSLParser#automatonDefDecl}.
 * @param ctx the parse tree
 */
fn enter_AutomatonDefDeclShift(&mut self, _ctx: &AutomatonDefDeclShiftContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code AutomatonDefDeclShift}
 * labeled alternative in {@link LibSLParser#automatonDefDecl}.
 * @param ctx the parse tree
 */
fn exit_AutomatonDefDeclShift(&mut self, _ctx: &AutomatonDefDeclShiftContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code AutomatonDefDeclConstructor}
 * labeled alternative in {@link LibSLParser#automatonDefDecl}.
 * @param ctx the parse tree
 */
fn enter_AutomatonDefDeclConstructor(&mut self, _ctx: &AutomatonDefDeclConstructorContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code AutomatonDefDeclConstructor}
 * labeled alternative in {@link LibSLParser#automatonDefDecl}.
 * @param ctx the parse tree
 */
fn exit_AutomatonDefDeclConstructor(&mut self, _ctx: &AutomatonDefDeclConstructorContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code AutomatonDefDeclDestructor}
 * labeled alternative in {@link LibSLParser#automatonDefDecl}.
 * @param ctx the parse tree
 */
fn enter_AutomatonDefDeclDestructor(&mut self, _ctx: &AutomatonDefDeclDestructorContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code AutomatonDefDeclDestructor}
 * labeled alternative in {@link LibSLParser#automatonDefDecl}.
 * @param ctx the parse tree
 */
fn exit_AutomatonDefDeclDestructor(&mut self, _ctx: &AutomatonDefDeclDestructorContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code AutomatonDefDeclProc}
 * labeled alternative in {@link LibSLParser#automatonDefDecl}.
 * @param ctx the parse tree
 */
fn enter_AutomatonDefDeclProc(&mut self, _ctx: &AutomatonDefDeclProcContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code AutomatonDefDeclProc}
 * labeled alternative in {@link LibSLParser#automatonDefDecl}.
 * @param ctx the parse tree
 */
fn exit_AutomatonDefDeclProc(&mut self, _ctx: &AutomatonDefDeclProcContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code AutomatonDefDeclFunction}
 * labeled alternative in {@link LibSLParser#automatonDefDecl}.
 * @param ctx the parse tree
 */
fn enter_AutomatonDefDeclFunction(&mut self, _ctx: &AutomatonDefDeclFunctionContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code AutomatonDefDeclFunction}
 * labeled alternative in {@link LibSLParser#automatonDefDecl}.
 * @param ctx the parse tree
 */
fn exit_AutomatonDefDeclFunction(&mut self, _ctx: &AutomatonDefDeclFunctionContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code AutomatonDefDeclVariable}
 * labeled alternative in {@link LibSLParser#automatonDefDecl}.
 * @param ctx the parse tree
 */
fn enter_AutomatonDefDeclVariable(&mut self, _ctx: &AutomatonDefDeclVariableContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code AutomatonDefDeclVariable}
 * labeled alternative in {@link LibSLParser#automatonDefDecl}.
 * @param ctx the parse tree
 */
fn exit_AutomatonDefDeclVariable(&mut self, _ctx: &AutomatonDefDeclVariableContext<'input>) { }
/**
 * Enter a parse tree produced by {@link LibSLParser#functionDecl}.
 * @param ctx the parse tree
 */
fn enter_functionDecl(&mut self, _ctx: &FunctionDeclContext<'input>) { }
/**
 * Exit a parse tree produced by {@link LibSLParser#functionDecl}.
 * @param ctx the parse tree
 */
fn exit_functionDecl(&mut self, _ctx: &FunctionDeclContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code FunctionModifierStatic}
 * labeled alternative in {@link LibSLParser#functionModifier}.
 * @param ctx the parse tree
 */
fn enter_FunctionModifierStatic(&mut self, _ctx: &FunctionModifierStaticContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code FunctionModifierStatic}
 * labeled alternative in {@link LibSLParser#functionModifier}.
 * @param ctx the parse tree
 */
fn exit_FunctionModifierStatic(&mut self, _ctx: &FunctionModifierStaticContext<'input>) { }
/**
 * Enter a parse tree produced by {@link LibSLParser#methodSpec}.
 * @param ctx the parse tree
 */
fn enter_methodSpec(&mut self, _ctx: &MethodSpecContext<'input>) { }
/**
 * Exit a parse tree produced by {@link LibSLParser#methodSpec}.
 * @param ctx the parse tree
 */
fn exit_methodSpec(&mut self, _ctx: &MethodSpecContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code FunctionDefBraced}
 * labeled alternative in {@link LibSLParser#functionDef}.
 * @param ctx the parse tree
 */
fn enter_FunctionDefBraced(&mut self, _ctx: &FunctionDefBracedContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code FunctionDefBraced}
 * labeled alternative in {@link LibSLParser#functionDef}.
 * @param ctx the parse tree
 */
fn exit_FunctionDefBraced(&mut self, _ctx: &FunctionDefBracedContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code FunctionDefSemicolon}
 * labeled alternative in {@link LibSLParser#functionDef}.
 * @param ctx the parse tree
 */
fn enter_FunctionDefSemicolon(&mut self, _ctx: &FunctionDefSemicolonContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code FunctionDefSemicolon}
 * labeled alternative in {@link LibSLParser#functionDef}.
 * @param ctx the parse tree
 */
fn exit_FunctionDefSemicolon(&mut self, _ctx: &FunctionDefSemicolonContext<'input>) { }
/**
 * Enter a parse tree produced by {@link LibSLParser#variableDecl}.
 * @param ctx the parse tree
 */
fn enter_variableDecl(&mut self, _ctx: &VariableDeclContext<'input>) { }
/**
 * Exit a parse tree produced by {@link LibSLParser#variableDecl}.
 * @param ctx the parse tree
 */
fn exit_variableDecl(&mut self, _ctx: &VariableDeclContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code VariableKindVar}
 * labeled alternative in {@link LibSLParser#variableKind}.
 * @param ctx the parse tree
 */
fn enter_VariableKindVar(&mut self, _ctx: &VariableKindVarContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code VariableKindVar}
 * labeled alternative in {@link LibSLParser#variableKind}.
 * @param ctx the parse tree
 */
fn exit_VariableKindVar(&mut self, _ctx: &VariableKindVarContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code VariableKindVal}
 * labeled alternative in {@link LibSLParser#variableKind}.
 * @param ctx the parse tree
 */
fn enter_VariableKindVal(&mut self, _ctx: &VariableKindValContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code VariableKindVal}
 * labeled alternative in {@link LibSLParser#variableKind}.
 * @param ctx the parse tree
 */
fn exit_VariableKindVal(&mut self, _ctx: &VariableKindValContext<'input>) { }
/**
 * Enter a parse tree produced by {@link LibSLParser#stateDecl}.
 * @param ctx the parse tree
 */
fn enter_stateDecl(&mut self, _ctx: &StateDeclContext<'input>) { }
/**
 * Exit a parse tree produced by {@link LibSLParser#stateDecl}.
 * @param ctx the parse tree
 */
fn exit_stateDecl(&mut self, _ctx: &StateDeclContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code StateKindInitial}
 * labeled alternative in {@link LibSLParser#stateKind}.
 * @param ctx the parse tree
 */
fn enter_StateKindInitial(&mut self, _ctx: &StateKindInitialContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code StateKindInitial}
 * labeled alternative in {@link LibSLParser#stateKind}.
 * @param ctx the parse tree
 */
fn exit_StateKindInitial(&mut self, _ctx: &StateKindInitialContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code StateKindRegular}
 * labeled alternative in {@link LibSLParser#stateKind}.
 * @param ctx the parse tree
 */
fn enter_StateKindRegular(&mut self, _ctx: &StateKindRegularContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code StateKindRegular}
 * labeled alternative in {@link LibSLParser#stateKind}.
 * @param ctx the parse tree
 */
fn exit_StateKindRegular(&mut self, _ctx: &StateKindRegularContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code StateKindFinal}
 * labeled alternative in {@link LibSLParser#stateKind}.
 * @param ctx the parse tree
 */
fn enter_StateKindFinal(&mut self, _ctx: &StateKindFinalContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code StateKindFinal}
 * labeled alternative in {@link LibSLParser#stateKind}.
 * @param ctx the parse tree
 */
fn exit_StateKindFinal(&mut self, _ctx: &StateKindFinalContext<'input>) { }
/**
 * Enter a parse tree produced by {@link LibSLParser#identList}.
 * @param ctx the parse tree
 */
fn enter_identList(&mut self, _ctx: &IdentListContext<'input>) { }
/**
 * Exit a parse tree produced by {@link LibSLParser#identList}.
 * @param ctx the parse tree
 */
fn exit_identList(&mut self, _ctx: &IdentListContext<'input>) { }
/**
 * Enter a parse tree produced by {@link LibSLParser#shiftDecl}.
 * @param ctx the parse tree
 */
fn enter_shiftDecl(&mut self, _ctx: &ShiftDeclContext<'input>) { }
/**
 * Exit a parse tree produced by {@link LibSLParser#shiftDecl}.
 * @param ctx the parse tree
 */
fn exit_shiftDecl(&mut self, _ctx: &ShiftDeclContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code ShiftSourceStateShorthand}
 * labeled alternative in {@link LibSLParser#shiftSourceState}.
 * @param ctx the parse tree
 */
fn enter_ShiftSourceStateShorthand(&mut self, _ctx: &ShiftSourceStateShorthandContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code ShiftSourceStateShorthand}
 * labeled alternative in {@link LibSLParser#shiftSourceState}.
 * @param ctx the parse tree
 */
fn exit_ShiftSourceStateShorthand(&mut self, _ctx: &ShiftSourceStateShorthandContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code ShiftSourceStateList}
 * labeled alternative in {@link LibSLParser#shiftSourceState}.
 * @param ctx the parse tree
 */
fn enter_ShiftSourceStateList(&mut self, _ctx: &ShiftSourceStateListContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code ShiftSourceStateList}
 * labeled alternative in {@link LibSLParser#shiftSourceState}.
 * @param ctx the parse tree
 */
fn exit_ShiftSourceStateList(&mut self, _ctx: &ShiftSourceStateListContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code ShiftByShorthand}
 * labeled alternative in {@link LibSLParser#shiftBy}.
 * @param ctx the parse tree
 */
fn enter_ShiftByShorthand(&mut self, _ctx: &ShiftByShorthandContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code ShiftByShorthand}
 * labeled alternative in {@link LibSLParser#shiftBy}.
 * @param ctx the parse tree
 */
fn exit_ShiftByShorthand(&mut self, _ctx: &ShiftByShorthandContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code ShiftByList}
 * labeled alternative in {@link LibSLParser#shiftBy}.
 * @param ctx the parse tree
 */
fn enter_ShiftByList(&mut self, _ctx: &ShiftByListContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code ShiftByList}
 * labeled alternative in {@link LibSLParser#shiftBy}.
 * @param ctx the parse tree
 */
fn exit_ShiftByList(&mut self, _ctx: &ShiftByListContext<'input>) { }
/**
 * Enter a parse tree produced by {@link LibSLParser#functionSignatureList}.
 * @param ctx the parse tree
 */
fn enter_functionSignatureList(&mut self, _ctx: &FunctionSignatureListContext<'input>) { }
/**
 * Exit a parse tree produced by {@link LibSLParser#functionSignatureList}.
 * @param ctx the parse tree
 */
fn exit_functionSignatureList(&mut self, _ctx: &FunctionSignatureListContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code FunctionSignatureShorthand}
 * labeled alternative in {@link LibSLParser#functionSignature}.
 * @param ctx the parse tree
 */
fn enter_FunctionSignatureShorthand(&mut self, _ctx: &FunctionSignatureShorthandContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code FunctionSignatureShorthand}
 * labeled alternative in {@link LibSLParser#functionSignature}.
 * @param ctx the parse tree
 */
fn exit_FunctionSignatureShorthand(&mut self, _ctx: &FunctionSignatureShorthandContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code FunctionSignatureQualified}
 * labeled alternative in {@link LibSLParser#functionSignature}.
 * @param ctx the parse tree
 */
fn enter_FunctionSignatureQualified(&mut self, _ctx: &FunctionSignatureQualifiedContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code FunctionSignatureQualified}
 * labeled alternative in {@link LibSLParser#functionSignature}.
 * @param ctx the parse tree
 */
fn exit_FunctionSignatureQualified(&mut self, _ctx: &FunctionSignatureQualifiedContext<'input>) { }
/**
 * Enter a parse tree produced by {@link LibSLParser#constructorDecl}.
 * @param ctx the parse tree
 */
fn enter_constructorDecl(&mut self, _ctx: &ConstructorDeclContext<'input>) { }
/**
 * Exit a parse tree produced by {@link LibSLParser#constructorDecl}.
 * @param ctx the parse tree
 */
fn exit_constructorDecl(&mut self, _ctx: &ConstructorDeclContext<'input>) { }
/**
 * Enter a parse tree produced by {@link LibSLParser#destructorDecl}.
 * @param ctx the parse tree
 */
fn enter_destructorDecl(&mut self, _ctx: &DestructorDeclContext<'input>) { }
/**
 * Exit a parse tree produced by {@link LibSLParser#destructorDecl}.
 * @param ctx the parse tree
 */
fn exit_destructorDecl(&mut self, _ctx: &DestructorDeclContext<'input>) { }
/**
 * Enter a parse tree produced by {@link LibSLParser#procDecl}.
 * @param ctx the parse tree
 */
fn enter_procDecl(&mut self, _ctx: &ProcDeclContext<'input>) { }
/**
 * Exit a parse tree produced by {@link LibSLParser#procDecl}.
 * @param ctx the parse tree
 */
fn exit_procDecl(&mut self, _ctx: &ProcDeclContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code ProcModifierPure}
 * labeled alternative in {@link LibSLParser#procModifier}.
 * @param ctx the parse tree
 */
fn enter_ProcModifierPure(&mut self, _ctx: &ProcModifierPureContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code ProcModifierPure}
 * labeled alternative in {@link LibSLParser#procModifier}.
 * @param ctx the parse tree
 */
fn exit_ProcModifierPure(&mut self, _ctx: &ProcModifierPureContext<'input>) { }
/**
 * Enter a parse tree produced by {@link LibSLParser#functionParamList}.
 * @param ctx the parse tree
 */
fn enter_functionParamList(&mut self, _ctx: &FunctionParamListContext<'input>) { }
/**
 * Exit a parse tree produced by {@link LibSLParser#functionParamList}.
 * @param ctx the parse tree
 */
fn exit_functionParamList(&mut self, _ctx: &FunctionParamListContext<'input>) { }
/**
 * Enter a parse tree produced by {@link LibSLParser#functionParam}.
 * @param ctx the parse tree
 */
fn enter_functionParam(&mut self, _ctx: &FunctionParamContext<'input>) { }
/**
 * Exit a parse tree produced by {@link LibSLParser#functionParam}.
 * @param ctx the parse tree
 */
fn exit_functionParam(&mut self, _ctx: &FunctionParamContext<'input>) { }
/**
 * Enter a parse tree produced by {@link LibSLParser#functionBody}.
 * @param ctx the parse tree
 */
fn enter_functionBody(&mut self, _ctx: &FunctionBodyContext<'input>) { }
/**
 * Exit a parse tree produced by {@link LibSLParser#functionBody}.
 * @param ctx the parse tree
 */
fn exit_functionBody(&mut self, _ctx: &FunctionBodyContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code ContractRequires}
 * labeled alternative in {@link LibSLParser#contract}.
 * @param ctx the parse tree
 */
fn enter_ContractRequires(&mut self, _ctx: &ContractRequiresContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code ContractRequires}
 * labeled alternative in {@link LibSLParser#contract}.
 * @param ctx the parse tree
 */
fn exit_ContractRequires(&mut self, _ctx: &ContractRequiresContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code ContractEnsures}
 * labeled alternative in {@link LibSLParser#contract}.
 * @param ctx the parse tree
 */
fn enter_ContractEnsures(&mut self, _ctx: &ContractEnsuresContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code ContractEnsures}
 * labeled alternative in {@link LibSLParser#contract}.
 * @param ctx the parse tree
 */
fn exit_ContractEnsures(&mut self, _ctx: &ContractEnsuresContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code ContractAssigns}
 * labeled alternative in {@link LibSLParser#contract}.
 * @param ctx the parse tree
 */
fn enter_ContractAssigns(&mut self, _ctx: &ContractAssignsContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code ContractAssigns}
 * labeled alternative in {@link LibSLParser#contract}.
 * @param ctx the parse tree
 */
fn exit_ContractAssigns(&mut self, _ctx: &ContractAssignsContext<'input>) { }
/**
 * Enter a parse tree produced by {@link LibSLParser#requiresContract}.
 * @param ctx the parse tree
 */
fn enter_requiresContract(&mut self, _ctx: &RequiresContractContext<'input>) { }
/**
 * Exit a parse tree produced by {@link LibSLParser#requiresContract}.
 * @param ctx the parse tree
 */
fn exit_requiresContract(&mut self, _ctx: &RequiresContractContext<'input>) { }
/**
 * Enter a parse tree produced by {@link LibSLParser#ensuresContract}.
 * @param ctx the parse tree
 */
fn enter_ensuresContract(&mut self, _ctx: &EnsuresContractContext<'input>) { }
/**
 * Exit a parse tree produced by {@link LibSLParser#ensuresContract}.
 * @param ctx the parse tree
 */
fn exit_ensuresContract(&mut self, _ctx: &EnsuresContractContext<'input>) { }
/**
 * Enter a parse tree produced by {@link LibSLParser#assignsContract}.
 * @param ctx the parse tree
 */
fn enter_assignsContract(&mut self, _ctx: &AssignsContractContext<'input>) { }
/**
 * Exit a parse tree produced by {@link LibSLParser#assignsContract}.
 * @param ctx the parse tree
 */
fn exit_assignsContract(&mut self, _ctx: &AssignsContractContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code ContractPredicateBlock}
 * labeled alternative in {@link LibSLParser#contractPredicate}.
 * @param ctx the parse tree
 */
fn enter_ContractPredicateBlock(&mut self, _ctx: &ContractPredicateBlockContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code ContractPredicateBlock}
 * labeled alternative in {@link LibSLParser#contractPredicate}.
 * @param ctx the parse tree
 */
fn exit_ContractPredicateBlock(&mut self, _ctx: &ContractPredicateBlockContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code ContractPredicateIf}
 * labeled alternative in {@link LibSLParser#contractPredicate}.
 * @param ctx the parse tree
 */
fn enter_ContractPredicateIf(&mut self, _ctx: &ContractPredicateIfContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code ContractPredicateIf}
 * labeled alternative in {@link LibSLParser#contractPredicate}.
 * @param ctx the parse tree
 */
fn exit_ContractPredicateIf(&mut self, _ctx: &ContractPredicateIfContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code ContractPredicateExpr}
 * labeled alternative in {@link LibSLParser#contractPredicate}.
 * @param ctx the parse tree
 */
fn enter_ContractPredicateExpr(&mut self, _ctx: &ContractPredicateExprContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code ContractPredicateExpr}
 * labeled alternative in {@link LibSLParser#contractPredicate}.
 * @param ctx the parse tree
 */
fn exit_ContractPredicateExpr(&mut self, _ctx: &ContractPredicateExprContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code ExprPredicateBlock}
 * labeled alternative in {@link LibSLParser#exprPredicate}.
 * @param ctx the parse tree
 */
fn enter_ExprPredicateBlock(&mut self, _ctx: &ExprPredicateBlockContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code ExprPredicateBlock}
 * labeled alternative in {@link LibSLParser#exprPredicate}.
 * @param ctx the parse tree
 */
fn exit_ExprPredicateBlock(&mut self, _ctx: &ExprPredicateBlockContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code ExprPredicateExpr}
 * labeled alternative in {@link LibSLParser#exprPredicate}.
 * @param ctx the parse tree
 */
fn enter_ExprPredicateExpr(&mut self, _ctx: &ExprPredicateExprContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code ExprPredicateExpr}
 * labeled alternative in {@link LibSLParser#exprPredicate}.
 * @param ctx the parse tree
 */
fn exit_ExprPredicateExpr(&mut self, _ctx: &ExprPredicateExprContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code PredicateBlock}
 * labeled alternative in {@link LibSLParser#predicate}.
 * @param ctx the parse tree
 */
fn enter_PredicateBlock(&mut self, _ctx: &PredicateBlockContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code PredicateBlock}
 * labeled alternative in {@link LibSLParser#predicate}.
 * @param ctx the parse tree
 */
fn exit_PredicateBlock(&mut self, _ctx: &PredicateBlockContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code PredicateNamed}
 * labeled alternative in {@link LibSLParser#predicate}.
 * @param ctx the parse tree
 */
fn enter_PredicateNamed(&mut self, _ctx: &PredicateNamedContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code PredicateNamed}
 * labeled alternative in {@link LibSLParser#predicate}.
 * @param ctx the parse tree
 */
fn exit_PredicateNamed(&mut self, _ctx: &PredicateNamedContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code PredicateVariableDecl}
 * labeled alternative in {@link LibSLParser#predicate}.
 * @param ctx the parse tree
 */
fn enter_PredicateVariableDecl(&mut self, _ctx: &PredicateVariableDeclContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code PredicateVariableDecl}
 * labeled alternative in {@link LibSLParser#predicate}.
 * @param ctx the parse tree
 */
fn exit_PredicateVariableDecl(&mut self, _ctx: &PredicateVariableDeclContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code PredicateIf}
 * labeled alternative in {@link LibSLParser#predicate}.
 * @param ctx the parse tree
 */
fn enter_PredicateIf(&mut self, _ctx: &PredicateIfContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code PredicateIf}
 * labeled alternative in {@link LibSLParser#predicate}.
 * @param ctx the parse tree
 */
fn exit_PredicateIf(&mut self, _ctx: &PredicateIfContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code PredicateExpr}
 * labeled alternative in {@link LibSLParser#predicate}.
 * @param ctx the parse tree
 */
fn enter_PredicateExpr(&mut self, _ctx: &PredicateExprContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code PredicateExpr}
 * labeled alternative in {@link LibSLParser#predicate}.
 * @param ctx the parse tree
 */
fn exit_PredicateExpr(&mut self, _ctx: &PredicateExprContext<'input>) { }
/**
 * Enter a parse tree produced by {@link LibSLParser#blockPredicate}.
 * @param ctx the parse tree
 */
fn enter_blockPredicate(&mut self, _ctx: &BlockPredicateContext<'input>) { }
/**
 * Exit a parse tree produced by {@link LibSLParser#blockPredicate}.
 * @param ctx the parse tree
 */
fn exit_blockPredicate(&mut self, _ctx: &BlockPredicateContext<'input>) { }
/**
 * Enter a parse tree produced by {@link LibSLParser#ifPredicate}.
 * @param ctx the parse tree
 */
fn enter_ifPredicate(&mut self, _ctx: &IfPredicateContext<'input>) { }
/**
 * Exit a parse tree produced by {@link LibSLParser#ifPredicate}.
 * @param ctx the parse tree
 */
fn exit_ifPredicate(&mut self, _ctx: &IfPredicateContext<'input>) { }
/**
 * Enter a parse tree produced by {@link LibSLParser#annotation}.
 * @param ctx the parse tree
 */
fn enter_annotation(&mut self, _ctx: &AnnotationContext<'input>) { }
/**
 * Exit a parse tree produced by {@link LibSLParser#annotation}.
 * @param ctx the parse tree
 */
fn exit_annotation(&mut self, _ctx: &AnnotationContext<'input>) { }
/**
 * Enter a parse tree produced by {@link LibSLParser#annotationArgList}.
 * @param ctx the parse tree
 */
fn enter_annotationArgList(&mut self, _ctx: &AnnotationArgListContext<'input>) { }
/**
 * Exit a parse tree produced by {@link LibSLParser#annotationArgList}.
 * @param ctx the parse tree
 */
fn exit_annotationArgList(&mut self, _ctx: &AnnotationArgListContext<'input>) { }
/**
 * Enter a parse tree produced by {@link LibSLParser#annotationArg}.
 * @param ctx the parse tree
 */
fn enter_annotationArg(&mut self, _ctx: &AnnotationArgContext<'input>) { }
/**
 * Exit a parse tree produced by {@link LibSLParser#annotationArg}.
 * @param ctx the parse tree
 */
fn exit_annotationArg(&mut self, _ctx: &AnnotationArgContext<'input>) { }
/**
 * Enter a parse tree produced by {@link LibSLParser#qualifiedTypeName}.
 * @param ctx the parse tree
 */
fn enter_qualifiedTypeName(&mut self, _ctx: &QualifiedTypeNameContext<'input>) { }
/**
 * Exit a parse tree produced by {@link LibSLParser#qualifiedTypeName}.
 * @param ctx the parse tree
 */
fn exit_qualifiedTypeName(&mut self, _ctx: &QualifiedTypeNameContext<'input>) { }
/**
 * Enter a parse tree produced by {@link LibSLParser#fullName}.
 * @param ctx the parse tree
 */
fn enter_fullName(&mut self, _ctx: &FullNameContext<'input>) { }
/**
 * Exit a parse tree produced by {@link LibSLParser#fullName}.
 * @param ctx the parse tree
 */
fn exit_fullName(&mut self, _ctx: &FullNameContext<'input>) { }
/**
 * Enter a parse tree produced by {@link LibSLParser#whereClause}.
 * @param ctx the parse tree
 */
fn enter_whereClause(&mut self, _ctx: &WhereClauseContext<'input>) { }
/**
 * Exit a parse tree produced by {@link LibSLParser#whereClause}.
 * @param ctx the parse tree
 */
fn exit_whereClause(&mut self, _ctx: &WhereClauseContext<'input>) { }
/**
 * Enter a parse tree produced by {@link LibSLParser#typeConstraint}.
 * @param ctx the parse tree
 */
fn enter_typeConstraint(&mut self, _ctx: &TypeConstraintContext<'input>) { }
/**
 * Exit a parse tree produced by {@link LibSLParser#typeConstraint}.
 * @param ctx the parse tree
 */
fn exit_typeConstraint(&mut self, _ctx: &TypeConstraintContext<'input>) { }
/**
 * Enter a parse tree produced by {@link LibSLParser#generics}.
 * @param ctx the parse tree
 */
fn enter_generics(&mut self, _ctx: &GenericsContext<'input>) { }
/**
 * Exit a parse tree produced by {@link LibSLParser#generics}.
 * @param ctx the parse tree
 */
fn exit_generics(&mut self, _ctx: &GenericsContext<'input>) { }
/**
 * Enter a parse tree produced by {@link LibSLParser#genericList}.
 * @param ctx the parse tree
 */
fn enter_genericList(&mut self, _ctx: &GenericListContext<'input>) { }
/**
 * Exit a parse tree produced by {@link LibSLParser#genericList}.
 * @param ctx the parse tree
 */
fn exit_genericList(&mut self, _ctx: &GenericListContext<'input>) { }
/**
 * Enter a parse tree produced by {@link LibSLParser#generic}.
 * @param ctx the parse tree
 */
fn enter_generic(&mut self, _ctx: &GenericContext<'input>) { }
/**
 * Exit a parse tree produced by {@link LibSLParser#generic}.
 * @param ctx the parse tree
 */
fn exit_generic(&mut self, _ctx: &GenericContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code Covariant}
 * labeled alternative in {@link LibSLParser#varianceSpec}.
 * @param ctx the parse tree
 */
fn enter_Covariant(&mut self, _ctx: &CovariantContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code Covariant}
 * labeled alternative in {@link LibSLParser#varianceSpec}.
 * @param ctx the parse tree
 */
fn exit_Covariant(&mut self, _ctx: &CovariantContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code Contravariant}
 * labeled alternative in {@link LibSLParser#varianceSpec}.
 * @param ctx the parse tree
 */
fn enter_Contravariant(&mut self, _ctx: &ContravariantContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code Contravariant}
 * labeled alternative in {@link LibSLParser#varianceSpec}.
 * @param ctx the parse tree
 */
fn exit_Contravariant(&mut self, _ctx: &ContravariantContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code Invariant}
 * labeled alternative in {@link LibSLParser#varianceSpec}.
 * @param ctx the parse tree
 */
fn enter_Invariant(&mut self, _ctx: &InvariantContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code Invariant}
 * labeled alternative in {@link LibSLParser#varianceSpec}.
 * @param ctx the parse tree
 */
fn exit_Invariant(&mut self, _ctx: &InvariantContext<'input>) { }
/**
 * Enter a parse tree produced by {@link LibSLParser#typeExprList}.
 * @param ctx the parse tree
 */
fn enter_typeExprList(&mut self, _ctx: &TypeExprListContext<'input>) { }
/**
 * Exit a parse tree produced by {@link LibSLParser#typeExprList}.
 * @param ctx the parse tree
 */
fn exit_typeExprList(&mut self, _ctx: &TypeExprListContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code TypeExprParen}
 * labeled alternative in {@link LibSLParser#atomicTypeExpr}.
 * @param ctx the parse tree
 */
fn enter_TypeExprParen(&mut self, _ctx: &TypeExprParenContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code TypeExprParen}
 * labeled alternative in {@link LibSLParser#atomicTypeExpr}.
 * @param ctx the parse tree
 */
fn exit_TypeExprParen(&mut self, _ctx: &TypeExprParenContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code TypeExprPrimitiveLit}
 * labeled alternative in {@link LibSLParser#atomicTypeExpr}.
 * @param ctx the parse tree
 */
fn enter_TypeExprPrimitiveLit(&mut self, _ctx: &TypeExprPrimitiveLitContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code TypeExprPrimitiveLit}
 * labeled alternative in {@link LibSLParser#atomicTypeExpr}.
 * @param ctx the parse tree
 */
fn exit_TypeExprPrimitiveLit(&mut self, _ctx: &TypeExprPrimitiveLitContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code TypeExprName}
 * labeled alternative in {@link LibSLParser#atomicTypeExpr}.
 * @param ctx the parse tree
 */
fn enter_TypeExprName(&mut self, _ctx: &TypeExprNameContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code TypeExprName}
 * labeled alternative in {@link LibSLParser#atomicTypeExpr}.
 * @param ctx the parse tree
 */
fn exit_TypeExprName(&mut self, _ctx: &TypeExprNameContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code TypeExprPointer}
 * labeled alternative in {@link LibSLParser#atomicTypeExpr}.
 * @param ctx the parse tree
 */
fn enter_TypeExprPointer(&mut self, _ctx: &TypeExprPointerContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code TypeExprPointer}
 * labeled alternative in {@link LibSLParser#atomicTypeExpr}.
 * @param ctx the parse tree
 */
fn exit_TypeExprPointer(&mut self, _ctx: &TypeExprPointerContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code TypeExprIntersection}
 * labeled alternative in {@link LibSLParser#typeExpr}.
 * @param ctx the parse tree
 */
fn enter_TypeExprIntersection(&mut self, _ctx: &TypeExprIntersectionContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code TypeExprIntersection}
 * labeled alternative in {@link LibSLParser#typeExpr}.
 * @param ctx the parse tree
 */
fn exit_TypeExprIntersection(&mut self, _ctx: &TypeExprIntersectionContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code TypeExprAtomic}
 * labeled alternative in {@link LibSLParser#typeExpr}.
 * @param ctx the parse tree
 */
fn enter_TypeExprAtomic(&mut self, _ctx: &TypeExprAtomicContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code TypeExprAtomic}
 * labeled alternative in {@link LibSLParser#typeExpr}.
 * @param ctx the parse tree
 */
fn exit_TypeExprAtomic(&mut self, _ctx: &TypeExprAtomicContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code TypeExprUnion}
 * labeled alternative in {@link LibSLParser#typeExpr}.
 * @param ctx the parse tree
 */
fn enter_TypeExprUnion(&mut self, _ctx: &TypeExprUnionContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code TypeExprUnion}
 * labeled alternative in {@link LibSLParser#typeExpr}.
 * @param ctx the parse tree
 */
fn exit_TypeExprUnion(&mut self, _ctx: &TypeExprUnionContext<'input>) { }
/**
 * Enter a parse tree produced by {@link LibSLParser#nameTypeExpr}.
 * @param ctx the parse tree
 */
fn enter_nameTypeExpr(&mut self, _ctx: &NameTypeExprContext<'input>) { }
/**
 * Exit a parse tree produced by {@link LibSLParser#nameTypeExpr}.
 * @param ctx the parse tree
 */
fn exit_nameTypeExpr(&mut self, _ctx: &NameTypeExprContext<'input>) { }
/**
 * Enter a parse tree produced by {@link LibSLParser#pointerTypeExpr}.
 * @param ctx the parse tree
 */
fn enter_pointerTypeExpr(&mut self, _ctx: &PointerTypeExprContext<'input>) { }
/**
 * Exit a parse tree produced by {@link LibSLParser#pointerTypeExpr}.
 * @param ctx the parse tree
 */
fn exit_pointerTypeExpr(&mut self, _ctx: &PointerTypeExprContext<'input>) { }
/**
 * Enter a parse tree produced by {@link LibSLParser#typeArgSpec}.
 * @param ctx the parse tree
 */
fn enter_typeArgSpec(&mut self, _ctx: &TypeArgSpecContext<'input>) { }
/**
 * Exit a parse tree produced by {@link LibSLParser#typeArgSpec}.
 * @param ctx the parse tree
 */
fn exit_typeArgSpec(&mut self, _ctx: &TypeArgSpecContext<'input>) { }
/**
 * Enter a parse tree produced by {@link LibSLParser#typeArgList}.
 * @param ctx the parse tree
 */
fn enter_typeArgList(&mut self, _ctx: &TypeArgListContext<'input>) { }
/**
 * Exit a parse tree produced by {@link LibSLParser#typeArgList}.
 * @param ctx the parse tree
 */
fn exit_typeArgList(&mut self, _ctx: &TypeArgListContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code TypeArgTypeExpr}
 * labeled alternative in {@link LibSLParser#typeArg}.
 * @param ctx the parse tree
 */
fn enter_TypeArgTypeExpr(&mut self, _ctx: &TypeArgTypeExprContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code TypeArgTypeExpr}
 * labeled alternative in {@link LibSLParser#typeArg}.
 * @param ctx the parse tree
 */
fn exit_TypeArgTypeExpr(&mut self, _ctx: &TypeArgTypeExprContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code TypeArgWildcard}
 * labeled alternative in {@link LibSLParser#typeArg}.
 * @param ctx the parse tree
 */
fn enter_TypeArgWildcard(&mut self, _ctx: &TypeArgWildcardContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code TypeArgWildcard}
 * labeled alternative in {@link LibSLParser#typeArg}.
 * @param ctx the parse tree
 */
fn exit_TypeArgWildcard(&mut self, _ctx: &TypeArgWildcardContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code BlockLoneStmt}
 * labeled alternative in {@link LibSLParser#block}.
 * @param ctx the parse tree
 */
fn enter_BlockLoneStmt(&mut self, _ctx: &BlockLoneStmtContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code BlockLoneStmt}
 * labeled alternative in {@link LibSLParser#block}.
 * @param ctx the parse tree
 */
fn exit_BlockLoneStmt(&mut self, _ctx: &BlockLoneStmtContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code BlockBraced}
 * labeled alternative in {@link LibSLParser#block}.
 * @param ctx the parse tree
 */
fn enter_BlockBraced(&mut self, _ctx: &BlockBracedContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code BlockBraced}
 * labeled alternative in {@link LibSLParser#block}.
 * @param ctx the parse tree
 */
fn exit_BlockBraced(&mut self, _ctx: &BlockBracedContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code StmtVariableDecl}
 * labeled alternative in {@link LibSLParser#stmt}.
 * @param ctx the parse tree
 */
fn enter_StmtVariableDecl(&mut self, _ctx: &StmtVariableDeclContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code StmtVariableDecl}
 * labeled alternative in {@link LibSLParser#stmt}.
 * @param ctx the parse tree
 */
fn exit_StmtVariableDecl(&mut self, _ctx: &StmtVariableDeclContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code StmtIf}
 * labeled alternative in {@link LibSLParser#stmt}.
 * @param ctx the parse tree
 */
fn enter_StmtIf(&mut self, _ctx: &StmtIfContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code StmtIf}
 * labeled alternative in {@link LibSLParser#stmt}.
 * @param ctx the parse tree
 */
fn exit_StmtIf(&mut self, _ctx: &StmtIfContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code StmtAssign}
 * labeled alternative in {@link LibSLParser#stmt}.
 * @param ctx the parse tree
 */
fn enter_StmtAssign(&mut self, _ctx: &StmtAssignContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code StmtAssign}
 * labeled alternative in {@link LibSLParser#stmt}.
 * @param ctx the parse tree
 */
fn exit_StmtAssign(&mut self, _ctx: &StmtAssignContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code StmtCancel}
 * labeled alternative in {@link LibSLParser#stmt}.
 * @param ctx the parse tree
 */
fn enter_StmtCancel(&mut self, _ctx: &StmtCancelContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code StmtCancel}
 * labeled alternative in {@link LibSLParser#stmt}.
 * @param ctx the parse tree
 */
fn exit_StmtCancel(&mut self, _ctx: &StmtCancelContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code StmtExpr}
 * labeled alternative in {@link LibSLParser#stmt}.
 * @param ctx the parse tree
 */
fn enter_StmtExpr(&mut self, _ctx: &StmtExprContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code StmtExpr}
 * labeled alternative in {@link LibSLParser#stmt}.
 * @param ctx the parse tree
 */
fn exit_StmtExpr(&mut self, _ctx: &StmtExprContext<'input>) { }
/**
 * Enter a parse tree produced by {@link LibSLParser#ifStmt}.
 * @param ctx the parse tree
 */
fn enter_ifStmt(&mut self, _ctx: &IfStmtContext<'input>) { }
/**
 * Exit a parse tree produced by {@link LibSLParser#ifStmt}.
 * @param ctx the parse tree
 */
fn exit_ifStmt(&mut self, _ctx: &IfStmtContext<'input>) { }
/**
 * Enter a parse tree produced by {@link LibSLParser#assignStmt}.
 * @param ctx the parse tree
 */
fn enter_assignStmt(&mut self, _ctx: &AssignStmtContext<'input>) { }
/**
 * Exit a parse tree produced by {@link LibSLParser#assignStmt}.
 * @param ctx the parse tree
 */
fn exit_assignStmt(&mut self, _ctx: &AssignStmtContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code AssigneeName}
 * labeled alternative in {@link LibSLParser#assignee}.
 * @param ctx the parse tree
 */
fn enter_AssigneeName(&mut self, _ctx: &AssigneeNameContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code AssigneeName}
 * labeled alternative in {@link LibSLParser#assignee}.
 * @param ctx the parse tree
 */
fn exit_AssigneeName(&mut self, _ctx: &AssigneeNameContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code AssigneeField}
 * labeled alternative in {@link LibSLParser#assignee}.
 * @param ctx the parse tree
 */
fn enter_AssigneeField(&mut self, _ctx: &AssigneeFieldContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code AssigneeField}
 * labeled alternative in {@link LibSLParser#assignee}.
 * @param ctx the parse tree
 */
fn exit_AssigneeField(&mut self, _ctx: &AssigneeFieldContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code AssigneeIndex}
 * labeled alternative in {@link LibSLParser#assignee}.
 * @param ctx the parse tree
 */
fn enter_AssigneeIndex(&mut self, _ctx: &AssigneeIndexContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code AssigneeIndex}
 * labeled alternative in {@link LibSLParser#assignee}.
 * @param ctx the parse tree
 */
fn exit_AssigneeIndex(&mut self, _ctx: &AssigneeIndexContext<'input>) { }
/**
 * Enter a parse tree produced by {@link LibSLParser#cancelStmt}.
 * @param ctx the parse tree
 */
fn enter_cancelStmt(&mut self, _ctx: &CancelStmtContext<'input>) { }
/**
 * Exit a parse tree produced by {@link LibSLParser#cancelStmt}.
 * @param ctx the parse tree
 */
fn exit_cancelStmt(&mut self, _ctx: &CancelStmtContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code OpAssign}
 * labeled alternative in {@link LibSLParser#assignOp}.
 * @param ctx the parse tree
 */
fn enter_OpAssign(&mut self, _ctx: &OpAssignContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code OpAssign}
 * labeled alternative in {@link LibSLParser#assignOp}.
 * @param ctx the parse tree
 */
fn exit_OpAssign(&mut self, _ctx: &OpAssignContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code OpAddAssign}
 * labeled alternative in {@link LibSLParser#assignOp}.
 * @param ctx the parse tree
 */
fn enter_OpAddAssign(&mut self, _ctx: &OpAddAssignContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code OpAddAssign}
 * labeled alternative in {@link LibSLParser#assignOp}.
 * @param ctx the parse tree
 */
fn exit_OpAddAssign(&mut self, _ctx: &OpAddAssignContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code OpSubAssign}
 * labeled alternative in {@link LibSLParser#assignOp}.
 * @param ctx the parse tree
 */
fn enter_OpSubAssign(&mut self, _ctx: &OpSubAssignContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code OpSubAssign}
 * labeled alternative in {@link LibSLParser#assignOp}.
 * @param ctx the parse tree
 */
fn exit_OpSubAssign(&mut self, _ctx: &OpSubAssignContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code OpMulAssign}
 * labeled alternative in {@link LibSLParser#assignOp}.
 * @param ctx the parse tree
 */
fn enter_OpMulAssign(&mut self, _ctx: &OpMulAssignContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code OpMulAssign}
 * labeled alternative in {@link LibSLParser#assignOp}.
 * @param ctx the parse tree
 */
fn exit_OpMulAssign(&mut self, _ctx: &OpMulAssignContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code OpDivAssign}
 * labeled alternative in {@link LibSLParser#assignOp}.
 * @param ctx the parse tree
 */
fn enter_OpDivAssign(&mut self, _ctx: &OpDivAssignContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code OpDivAssign}
 * labeled alternative in {@link LibSLParser#assignOp}.
 * @param ctx the parse tree
 */
fn exit_OpDivAssign(&mut self, _ctx: &OpDivAssignContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code OpModAssign}
 * labeled alternative in {@link LibSLParser#assignOp}.
 * @param ctx the parse tree
 */
fn enter_OpModAssign(&mut self, _ctx: &OpModAssignContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code OpModAssign}
 * labeled alternative in {@link LibSLParser#assignOp}.
 * @param ctx the parse tree
 */
fn exit_OpModAssign(&mut self, _ctx: &OpModAssignContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code OpBitAndAssign}
 * labeled alternative in {@link LibSLParser#assignOp}.
 * @param ctx the parse tree
 */
fn enter_OpBitAndAssign(&mut self, _ctx: &OpBitAndAssignContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code OpBitAndAssign}
 * labeled alternative in {@link LibSLParser#assignOp}.
 * @param ctx the parse tree
 */
fn exit_OpBitAndAssign(&mut self, _ctx: &OpBitAndAssignContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code OpBitOrAssign}
 * labeled alternative in {@link LibSLParser#assignOp}.
 * @param ctx the parse tree
 */
fn enter_OpBitOrAssign(&mut self, _ctx: &OpBitOrAssignContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code OpBitOrAssign}
 * labeled alternative in {@link LibSLParser#assignOp}.
 * @param ctx the parse tree
 */
fn exit_OpBitOrAssign(&mut self, _ctx: &OpBitOrAssignContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code OpBitXorAssign}
 * labeled alternative in {@link LibSLParser#assignOp}.
 * @param ctx the parse tree
 */
fn enter_OpBitXorAssign(&mut self, _ctx: &OpBitXorAssignContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code OpBitXorAssign}
 * labeled alternative in {@link LibSLParser#assignOp}.
 * @param ctx the parse tree
 */
fn exit_OpBitXorAssign(&mut self, _ctx: &OpBitXorAssignContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code OpLShiftAssign}
 * labeled alternative in {@link LibSLParser#assignOp}.
 * @param ctx the parse tree
 */
fn enter_OpLShiftAssign(&mut self, _ctx: &OpLShiftAssignContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code OpLShiftAssign}
 * labeled alternative in {@link LibSLParser#assignOp}.
 * @param ctx the parse tree
 */
fn exit_OpLShiftAssign(&mut self, _ctx: &OpLShiftAssignContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code OpRShiftAssign}
 * labeled alternative in {@link LibSLParser#assignOp}.
 * @param ctx the parse tree
 */
fn enter_OpRShiftAssign(&mut self, _ctx: &OpRShiftAssignContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code OpRShiftAssign}
 * labeled alternative in {@link LibSLParser#assignOp}.
 * @param ctx the parse tree
 */
fn exit_OpRShiftAssign(&mut self, _ctx: &OpRShiftAssignContext<'input>) { }
/**
 * Enter a parse tree produced by {@link LibSLParser#exprList}.
 * @param ctx the parse tree
 */
fn enter_exprList(&mut self, _ctx: &ExprListContext<'input>) { }
/**
 * Exit a parse tree produced by {@link LibSLParser#exprList}.
 * @param ctx the parse tree
 */
fn exit_exprList(&mut self, _ctx: &ExprListContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code AtomicExprParen}
 * labeled alternative in {@link LibSLParser#atomicExpr}.
 * @param ctx the parse tree
 */
fn enter_AtomicExprParen(&mut self, _ctx: &AtomicExprParenContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code AtomicExprParen}
 * labeled alternative in {@link LibSLParser#atomicExpr}.
 * @param ctx the parse tree
 */
fn exit_AtomicExprParen(&mut self, _ctx: &AtomicExprParenContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code AtomicExprPrimitiveLit}
 * labeled alternative in {@link LibSLParser#atomicExpr}.
 * @param ctx the parse tree
 */
fn enter_AtomicExprPrimitiveLit(&mut self, _ctx: &AtomicExprPrimitiveLitContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code AtomicExprPrimitiveLit}
 * labeled alternative in {@link LibSLParser#atomicExpr}.
 * @param ctx the parse tree
 */
fn exit_AtomicExprPrimitiveLit(&mut self, _ctx: &AtomicExprPrimitiveLitContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code AtomicExprSignedNumLit}
 * labeled alternative in {@link LibSLParser#atomicExpr}.
 * @param ctx the parse tree
 */
fn enter_AtomicExprSignedNumLit(&mut self, _ctx: &AtomicExprSignedNumLitContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code AtomicExprSignedNumLit}
 * labeled alternative in {@link LibSLParser#atomicExpr}.
 * @param ctx the parse tree
 */
fn exit_AtomicExprSignedNumLit(&mut self, _ctx: &AtomicExprSignedNumLitContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code AtomicExprArrayLit}
 * labeled alternative in {@link LibSLParser#atomicExpr}.
 * @param ctx the parse tree
 */
fn enter_AtomicExprArrayLit(&mut self, _ctx: &AtomicExprArrayLitContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code AtomicExprArrayLit}
 * labeled alternative in {@link LibSLParser#atomicExpr}.
 * @param ctx the parse tree
 */
fn exit_AtomicExprArrayLit(&mut self, _ctx: &AtomicExprArrayLitContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code AtomicExprSetLit}
 * labeled alternative in {@link LibSLParser#atomicExpr}.
 * @param ctx the parse tree
 */
fn enter_AtomicExprSetLit(&mut self, _ctx: &AtomicExprSetLitContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code AtomicExprSetLit}
 * labeled alternative in {@link LibSLParser#atomicExpr}.
 * @param ctx the parse tree
 */
fn exit_AtomicExprSetLit(&mut self, _ctx: &AtomicExprSetLitContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code AtomicExprName}
 * labeled alternative in {@link LibSLParser#atomicExpr}.
 * @param ctx the parse tree
 */
fn enter_AtomicExprName(&mut self, _ctx: &AtomicExprNameContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code AtomicExprName}
 * labeled alternative in {@link LibSLParser#atomicExpr}.
 * @param ctx the parse tree
 */
fn exit_AtomicExprName(&mut self, _ctx: &AtomicExprNameContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code SignedNumLitInt}
 * labeled alternative in {@link LibSLParser#signedNumLit}.
 * @param ctx the parse tree
 */
fn enter_SignedNumLitInt(&mut self, _ctx: &SignedNumLitIntContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code SignedNumLitInt}
 * labeled alternative in {@link LibSLParser#signedNumLit}.
 * @param ctx the parse tree
 */
fn exit_SignedNumLitInt(&mut self, _ctx: &SignedNumLitIntContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code SignedNumLitFloat}
 * labeled alternative in {@link LibSLParser#signedNumLit}.
 * @param ctx the parse tree
 */
fn enter_SignedNumLitFloat(&mut self, _ctx: &SignedNumLitFloatContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code SignedNumLitFloat}
 * labeled alternative in {@link LibSLParser#signedNumLit}.
 * @param ctx the parse tree
 */
fn exit_SignedNumLitFloat(&mut self, _ctx: &SignedNumLitFloatContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code ExprProcCallUnqualified}
 * labeled alternative in {@link LibSLParser#expr}.
 * @param ctx the parse tree
 */
fn enter_ExprProcCallUnqualified(&mut self, _ctx: &ExprProcCallUnqualifiedContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code ExprProcCallUnqualified}
 * labeled alternative in {@link LibSLParser#expr}.
 * @param ctx the parse tree
 */
fn exit_ExprProcCallUnqualified(&mut self, _ctx: &ExprProcCallUnqualifiedContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code ExprPrev}
 * labeled alternative in {@link LibSLParser#expr}.
 * @param ctx the parse tree
 */
fn enter_ExprPrev(&mut self, _ctx: &ExprPrevContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code ExprPrev}
 * labeled alternative in {@link LibSLParser#expr}.
 * @param ctx the parse tree
 */
fn exit_ExprPrev(&mut self, _ctx: &ExprPrevContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code ExprActionCall}
 * labeled alternative in {@link LibSLParser#expr}.
 * @param ctx the parse tree
 */
fn enter_ExprActionCall(&mut self, _ctx: &ExprActionCallContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code ExprActionCall}
 * labeled alternative in {@link LibSLParser#expr}.
 * @param ctx the parse tree
 */
fn exit_ExprActionCall(&mut self, _ctx: &ExprActionCallContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code ExprBitXor}
 * labeled alternative in {@link LibSLParser#expr}.
 * @param ctx the parse tree
 */
fn enter_ExprBitXor(&mut self, _ctx: &ExprBitXorContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code ExprBitXor}
 * labeled alternative in {@link LibSLParser#expr}.
 * @param ctx the parse tree
 */
fn exit_ExprBitXor(&mut self, _ctx: &ExprBitXorContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code ExprIndex}
 * labeled alternative in {@link LibSLParser#expr}.
 * @param ctx the parse tree
 */
fn enter_ExprIndex(&mut self, _ctx: &ExprIndexContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code ExprIndex}
 * labeled alternative in {@link LibSLParser#expr}.
 * @param ctx the parse tree
 */
fn exit_ExprIndex(&mut self, _ctx: &ExprIndexContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code ExprHasConcept}
 * labeled alternative in {@link LibSLParser#expr}.
 * @param ctx the parse tree
 */
fn enter_ExprHasConcept(&mut self, _ctx: &ExprHasConceptContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code ExprHasConcept}
 * labeled alternative in {@link LibSLParser#expr}.
 * @param ctx the parse tree
 */
fn exit_ExprHasConcept(&mut self, _ctx: &ExprHasConceptContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code ExprTypeComparison}
 * labeled alternative in {@link LibSLParser#expr}.
 * @param ctx the parse tree
 */
fn enter_ExprTypeComparison(&mut self, _ctx: &ExprTypeComparisonContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code ExprTypeComparison}
 * labeled alternative in {@link LibSLParser#expr}.
 * @param ctx the parse tree
 */
fn exit_ExprTypeComparison(&mut self, _ctx: &ExprTypeComparisonContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code ExprArrayLit}
 * labeled alternative in {@link LibSLParser#expr}.
 * @param ctx the parse tree
 */
fn enter_ExprArrayLit(&mut self, _ctx: &ExprArrayLitContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code ExprArrayLit}
 * labeled alternative in {@link LibSLParser#expr}.
 * @param ctx the parse tree
 */
fn exit_ExprArrayLit(&mut self, _ctx: &ExprArrayLitContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code ExprOr}
 * labeled alternative in {@link LibSLParser#expr}.
 * @param ctx the parse tree
 */
fn enter_ExprOr(&mut self, _ctx: &ExprOrContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code ExprOr}
 * labeled alternative in {@link LibSLParser#expr}.
 * @param ctx the parse tree
 */
fn exit_ExprOr(&mut self, _ctx: &ExprOrContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code ExprCast}
 * labeled alternative in {@link LibSLParser#expr}.
 * @param ctx the parse tree
 */
fn enter_ExprCast(&mut self, _ctx: &ExprCastContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code ExprCast}
 * labeled alternative in {@link LibSLParser#expr}.
 * @param ctx the parse tree
 */
fn exit_ExprCast(&mut self, _ctx: &ExprCastContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code ExprPrimitiveLit}
 * labeled alternative in {@link LibSLParser#expr}.
 * @param ctx the parse tree
 */
fn enter_ExprPrimitiveLit(&mut self, _ctx: &ExprPrimitiveLitContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code ExprPrimitiveLit}
 * labeled alternative in {@link LibSLParser#expr}.
 * @param ctx the parse tree
 */
fn exit_ExprPrimitiveLit(&mut self, _ctx: &ExprPrimitiveLitContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code ExprMultiplicative}
 * labeled alternative in {@link LibSLParser#expr}.
 * @param ctx the parse tree
 */
fn enter_ExprMultiplicative(&mut self, _ctx: &ExprMultiplicativeContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code ExprMultiplicative}
 * labeled alternative in {@link LibSLParser#expr}.
 * @param ctx the parse tree
 */
fn exit_ExprMultiplicative(&mut self, _ctx: &ExprMultiplicativeContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code ExprSetLit}
 * labeled alternative in {@link LibSLParser#expr}.
 * @param ctx the parse tree
 */
fn enter_ExprSetLit(&mut self, _ctx: &ExprSetLitContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code ExprSetLit}
 * labeled alternative in {@link LibSLParser#expr}.
 * @param ctx the parse tree
 */
fn exit_ExprSetLit(&mut self, _ctx: &ExprSetLitContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code ExprParen}
 * labeled alternative in {@link LibSLParser#expr}.
 * @param ctx the parse tree
 */
fn enter_ExprParen(&mut self, _ctx: &ExprParenContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code ExprParen}
 * labeled alternative in {@link LibSLParser#expr}.
 * @param ctx the parse tree
 */
fn exit_ExprParen(&mut self, _ctx: &ExprParenContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code ExprInstantiation}
 * labeled alternative in {@link LibSLParser#expr}.
 * @param ctx the parse tree
 */
fn enter_ExprInstantiation(&mut self, _ctx: &ExprInstantiationContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code ExprInstantiation}
 * labeled alternative in {@link LibSLParser#expr}.
 * @param ctx the parse tree
 */
fn exit_ExprInstantiation(&mut self, _ctx: &ExprInstantiationContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code ExprName}
 * labeled alternative in {@link LibSLParser#expr}.
 * @param ctx the parse tree
 */
fn enter_ExprName(&mut self, _ctx: &ExprNameContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code ExprName}
 * labeled alternative in {@link LibSLParser#expr}.
 * @param ctx the parse tree
 */
fn exit_ExprName(&mut self, _ctx: &ExprNameContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code ExprField}
 * labeled alternative in {@link LibSLParser#expr}.
 * @param ctx the parse tree
 */
fn enter_ExprField(&mut self, _ctx: &ExprFieldContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code ExprField}
 * labeled alternative in {@link LibSLParser#expr}.
 * @param ctx the parse tree
 */
fn exit_ExprField(&mut self, _ctx: &ExprFieldContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code ExprRelational}
 * labeled alternative in {@link LibSLParser#expr}.
 * @param ctx the parse tree
 */
fn enter_ExprRelational(&mut self, _ctx: &ExprRelationalContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code ExprRelational}
 * labeled alternative in {@link LibSLParser#expr}.
 * @param ctx the parse tree
 */
fn exit_ExprRelational(&mut self, _ctx: &ExprRelationalContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code ExprShift}
 * labeled alternative in {@link LibSLParser#expr}.
 * @param ctx the parse tree
 */
fn enter_ExprShift(&mut self, _ctx: &ExprShiftContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code ExprShift}
 * labeled alternative in {@link LibSLParser#expr}.
 * @param ctx the parse tree
 */
fn exit_ExprShift(&mut self, _ctx: &ExprShiftContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code ExprAdditive}
 * labeled alternative in {@link LibSLParser#expr}.
 * @param ctx the parse tree
 */
fn enter_ExprAdditive(&mut self, _ctx: &ExprAdditiveContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code ExprAdditive}
 * labeled alternative in {@link LibSLParser#expr}.
 * @param ctx the parse tree
 */
fn exit_ExprAdditive(&mut self, _ctx: &ExprAdditiveContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code ExprBitOr}
 * labeled alternative in {@link LibSLParser#expr}.
 * @param ctx the parse tree
 */
fn enter_ExprBitOr(&mut self, _ctx: &ExprBitOrContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code ExprBitOr}
 * labeled alternative in {@link LibSLParser#expr}.
 * @param ctx the parse tree
 */
fn exit_ExprBitOr(&mut self, _ctx: &ExprBitOrContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code ExprAnd}
 * labeled alternative in {@link LibSLParser#expr}.
 * @param ctx the parse tree
 */
fn enter_ExprAnd(&mut self, _ctx: &ExprAndContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code ExprAnd}
 * labeled alternative in {@link LibSLParser#expr}.
 * @param ctx the parse tree
 */
fn exit_ExprAnd(&mut self, _ctx: &ExprAndContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code ExprDeref}
 * labeled alternative in {@link LibSLParser#expr}.
 * @param ctx the parse tree
 */
fn enter_ExprDeref(&mut self, _ctx: &ExprDerefContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code ExprDeref}
 * labeled alternative in {@link LibSLParser#expr}.
 * @param ctx the parse tree
 */
fn exit_ExprDeref(&mut self, _ctx: &ExprDerefContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code ExprUnary}
 * labeled alternative in {@link LibSLParser#expr}.
 * @param ctx the parse tree
 */
fn enter_ExprUnary(&mut self, _ctx: &ExprUnaryContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code ExprUnary}
 * labeled alternative in {@link LibSLParser#expr}.
 * @param ctx the parse tree
 */
fn exit_ExprUnary(&mut self, _ctx: &ExprUnaryContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code ExprProcCallQualified}
 * labeled alternative in {@link LibSLParser#expr}.
 * @param ctx the parse tree
 */
fn enter_ExprProcCallQualified(&mut self, _ctx: &ExprProcCallQualifiedContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code ExprProcCallQualified}
 * labeled alternative in {@link LibSLParser#expr}.
 * @param ctx the parse tree
 */
fn exit_ExprProcCallQualified(&mut self, _ctx: &ExprProcCallQualifiedContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code ExprBitAnd}
 * labeled alternative in {@link LibSLParser#expr}.
 * @param ctx the parse tree
 */
fn enter_ExprBitAnd(&mut self, _ctx: &ExprBitAndContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code ExprBitAnd}
 * labeled alternative in {@link LibSLParser#expr}.
 * @param ctx the parse tree
 */
fn exit_ExprBitAnd(&mut self, _ctx: &ExprBitAndContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code UnOpPlus}
 * labeled alternative in {@link LibSLParser#unOp}.
 * @param ctx the parse tree
 */
fn enter_UnOpPlus(&mut self, _ctx: &UnOpPlusContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code UnOpPlus}
 * labeled alternative in {@link LibSLParser#unOp}.
 * @param ctx the parse tree
 */
fn exit_UnOpPlus(&mut self, _ctx: &UnOpPlusContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code UnOpNeg}
 * labeled alternative in {@link LibSLParser#unOp}.
 * @param ctx the parse tree
 */
fn enter_UnOpNeg(&mut self, _ctx: &UnOpNegContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code UnOpNeg}
 * labeled alternative in {@link LibSLParser#unOp}.
 * @param ctx the parse tree
 */
fn exit_UnOpNeg(&mut self, _ctx: &UnOpNegContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code UnOpBitNot}
 * labeled alternative in {@link LibSLParser#unOp}.
 * @param ctx the parse tree
 */
fn enter_UnOpBitNot(&mut self, _ctx: &UnOpBitNotContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code UnOpBitNot}
 * labeled alternative in {@link LibSLParser#unOp}.
 * @param ctx the parse tree
 */
fn exit_UnOpBitNot(&mut self, _ctx: &UnOpBitNotContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code UnOpNot}
 * labeled alternative in {@link LibSLParser#unOp}.
 * @param ctx the parse tree
 */
fn enter_UnOpNot(&mut self, _ctx: &UnOpNotContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code UnOpNot}
 * labeled alternative in {@link LibSLParser#unOp}.
 * @param ctx the parse tree
 */
fn exit_UnOpNot(&mut self, _ctx: &UnOpNotContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code BinOpMul}
 * labeled alternative in {@link LibSLParser#mulBinOp}.
 * @param ctx the parse tree
 */
fn enter_BinOpMul(&mut self, _ctx: &BinOpMulContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code BinOpMul}
 * labeled alternative in {@link LibSLParser#mulBinOp}.
 * @param ctx the parse tree
 */
fn exit_BinOpMul(&mut self, _ctx: &BinOpMulContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code BinOpDiv}
 * labeled alternative in {@link LibSLParser#mulBinOp}.
 * @param ctx the parse tree
 */
fn enter_BinOpDiv(&mut self, _ctx: &BinOpDivContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code BinOpDiv}
 * labeled alternative in {@link LibSLParser#mulBinOp}.
 * @param ctx the parse tree
 */
fn exit_BinOpDiv(&mut self, _ctx: &BinOpDivContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code BinOpMod}
 * labeled alternative in {@link LibSLParser#mulBinOp}.
 * @param ctx the parse tree
 */
fn enter_BinOpMod(&mut self, _ctx: &BinOpModContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code BinOpMod}
 * labeled alternative in {@link LibSLParser#mulBinOp}.
 * @param ctx the parse tree
 */
fn exit_BinOpMod(&mut self, _ctx: &BinOpModContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code BinOpAdd}
 * labeled alternative in {@link LibSLParser#addBinOp}.
 * @param ctx the parse tree
 */
fn enter_BinOpAdd(&mut self, _ctx: &BinOpAddContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code BinOpAdd}
 * labeled alternative in {@link LibSLParser#addBinOp}.
 * @param ctx the parse tree
 */
fn exit_BinOpAdd(&mut self, _ctx: &BinOpAddContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code BinOpSub}
 * labeled alternative in {@link LibSLParser#addBinOp}.
 * @param ctx the parse tree
 */
fn enter_BinOpSub(&mut self, _ctx: &BinOpSubContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code BinOpSub}
 * labeled alternative in {@link LibSLParser#addBinOp}.
 * @param ctx the parse tree
 */
fn exit_BinOpSub(&mut self, _ctx: &BinOpSubContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code BinOpLogicalLeft}
 * labeled alternative in {@link LibSLParser#bitShiftOp}.
 * @param ctx the parse tree
 */
fn enter_BinOpLogicalLeft(&mut self, _ctx: &BinOpLogicalLeftContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code BinOpLogicalLeft}
 * labeled alternative in {@link LibSLParser#bitShiftOp}.
 * @param ctx the parse tree
 */
fn exit_BinOpLogicalLeft(&mut self, _ctx: &BinOpLogicalLeftContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code BinOpLogicalRight}
 * labeled alternative in {@link LibSLParser#bitShiftOp}.
 * @param ctx the parse tree
 */
fn enter_BinOpLogicalRight(&mut self, _ctx: &BinOpLogicalRightContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code BinOpLogicalRight}
 * labeled alternative in {@link LibSLParser#bitShiftOp}.
 * @param ctx the parse tree
 */
fn exit_BinOpLogicalRight(&mut self, _ctx: &BinOpLogicalRightContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code BinOpArithmeticLeft}
 * labeled alternative in {@link LibSLParser#bitShiftOp}.
 * @param ctx the parse tree
 */
fn enter_BinOpArithmeticLeft(&mut self, _ctx: &BinOpArithmeticLeftContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code BinOpArithmeticLeft}
 * labeled alternative in {@link LibSLParser#bitShiftOp}.
 * @param ctx the parse tree
 */
fn exit_BinOpArithmeticLeft(&mut self, _ctx: &BinOpArithmeticLeftContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code BinOpArithmeticRight}
 * labeled alternative in {@link LibSLParser#bitShiftOp}.
 * @param ctx the parse tree
 */
fn enter_BinOpArithmeticRight(&mut self, _ctx: &BinOpArithmeticRightContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code BinOpArithmeticRight}
 * labeled alternative in {@link LibSLParser#bitShiftOp}.
 * @param ctx the parse tree
 */
fn exit_BinOpArithmeticRight(&mut self, _ctx: &BinOpArithmeticRightContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code BinOpLessEquals}
 * labeled alternative in {@link LibSLParser#relOp}.
 * @param ctx the parse tree
 */
fn enter_BinOpLessEquals(&mut self, _ctx: &BinOpLessEqualsContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code BinOpLessEquals}
 * labeled alternative in {@link LibSLParser#relOp}.
 * @param ctx the parse tree
 */
fn exit_BinOpLessEquals(&mut self, _ctx: &BinOpLessEqualsContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code BinOpGreaterEquals}
 * labeled alternative in {@link LibSLParser#relOp}.
 * @param ctx the parse tree
 */
fn enter_BinOpGreaterEquals(&mut self, _ctx: &BinOpGreaterEqualsContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code BinOpGreaterEquals}
 * labeled alternative in {@link LibSLParser#relOp}.
 * @param ctx the parse tree
 */
fn exit_BinOpGreaterEquals(&mut self, _ctx: &BinOpGreaterEqualsContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code BinOpLess}
 * labeled alternative in {@link LibSLParser#relOp}.
 * @param ctx the parse tree
 */
fn enter_BinOpLess(&mut self, _ctx: &BinOpLessContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code BinOpLess}
 * labeled alternative in {@link LibSLParser#relOp}.
 * @param ctx the parse tree
 */
fn exit_BinOpLess(&mut self, _ctx: &BinOpLessContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code BinOpGreater}
 * labeled alternative in {@link LibSLParser#relOp}.
 * @param ctx the parse tree
 */
fn enter_BinOpGreater(&mut self, _ctx: &BinOpGreaterContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code BinOpGreater}
 * labeled alternative in {@link LibSLParser#relOp}.
 * @param ctx the parse tree
 */
fn exit_BinOpGreater(&mut self, _ctx: &BinOpGreaterContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code BinOpEquals}
 * labeled alternative in {@link LibSLParser#relOp}.
 * @param ctx the parse tree
 */
fn enter_BinOpEquals(&mut self, _ctx: &BinOpEqualsContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code BinOpEquals}
 * labeled alternative in {@link LibSLParser#relOp}.
 * @param ctx the parse tree
 */
fn exit_BinOpEquals(&mut self, _ctx: &BinOpEqualsContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code BinOpNotEquals}
 * labeled alternative in {@link LibSLParser#relOp}.
 * @param ctx the parse tree
 */
fn enter_BinOpNotEquals(&mut self, _ctx: &BinOpNotEqualsContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code BinOpNotEquals}
 * labeled alternative in {@link LibSLParser#relOp}.
 * @param ctx the parse tree
 */
fn exit_BinOpNotEquals(&mut self, _ctx: &BinOpNotEqualsContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code BinOpIn}
 * labeled alternative in {@link LibSLParser#relOp}.
 * @param ctx the parse tree
 */
fn enter_BinOpIn(&mut self, _ctx: &BinOpInContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code BinOpIn}
 * labeled alternative in {@link LibSLParser#relOp}.
 * @param ctx the parse tree
 */
fn exit_BinOpIn(&mut self, _ctx: &BinOpInContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code PrimitiveLitInt}
 * labeled alternative in {@link LibSLParser#primitiveLit}.
 * @param ctx the parse tree
 */
fn enter_PrimitiveLitInt(&mut self, _ctx: &PrimitiveLitIntContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code PrimitiveLitInt}
 * labeled alternative in {@link LibSLParser#primitiveLit}.
 * @param ctx the parse tree
 */
fn exit_PrimitiveLitInt(&mut self, _ctx: &PrimitiveLitIntContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code PrimitiveLitFloat}
 * labeled alternative in {@link LibSLParser#primitiveLit}.
 * @param ctx the parse tree
 */
fn enter_PrimitiveLitFloat(&mut self, _ctx: &PrimitiveLitFloatContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code PrimitiveLitFloat}
 * labeled alternative in {@link LibSLParser#primitiveLit}.
 * @param ctx the parse tree
 */
fn exit_PrimitiveLitFloat(&mut self, _ctx: &PrimitiveLitFloatContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code PrimitiveLitStringLit}
 * labeled alternative in {@link LibSLParser#primitiveLit}.
 * @param ctx the parse tree
 */
fn enter_PrimitiveLitStringLit(&mut self, _ctx: &PrimitiveLitStringLitContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code PrimitiveLitStringLit}
 * labeled alternative in {@link LibSLParser#primitiveLit}.
 * @param ctx the parse tree
 */
fn exit_PrimitiveLitStringLit(&mut self, _ctx: &PrimitiveLitStringLitContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code PrimitiveLitChar}
 * labeled alternative in {@link LibSLParser#primitiveLit}.
 * @param ctx the parse tree
 */
fn enter_PrimitiveLitChar(&mut self, _ctx: &PrimitiveLitCharContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code PrimitiveLitChar}
 * labeled alternative in {@link LibSLParser#primitiveLit}.
 * @param ctx the parse tree
 */
fn exit_PrimitiveLitChar(&mut self, _ctx: &PrimitiveLitCharContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code PrimitiveLitTrue}
 * labeled alternative in {@link LibSLParser#primitiveLit}.
 * @param ctx the parse tree
 */
fn enter_PrimitiveLitTrue(&mut self, _ctx: &PrimitiveLitTrueContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code PrimitiveLitTrue}
 * labeled alternative in {@link LibSLParser#primitiveLit}.
 * @param ctx the parse tree
 */
fn exit_PrimitiveLitTrue(&mut self, _ctx: &PrimitiveLitTrueContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code PrimitiveLitFalse}
 * labeled alternative in {@link LibSLParser#primitiveLit}.
 * @param ctx the parse tree
 */
fn enter_PrimitiveLitFalse(&mut self, _ctx: &PrimitiveLitFalseContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code PrimitiveLitFalse}
 * labeled alternative in {@link LibSLParser#primitiveLit}.
 * @param ctx the parse tree
 */
fn exit_PrimitiveLitFalse(&mut self, _ctx: &PrimitiveLitFalseContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code PrimitiveLitNull}
 * labeled alternative in {@link LibSLParser#primitiveLit}.
 * @param ctx the parse tree
 */
fn enter_PrimitiveLitNull(&mut self, _ctx: &PrimitiveLitNullContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code PrimitiveLitNull}
 * labeled alternative in {@link LibSLParser#primitiveLit}.
 * @param ctx the parse tree
 */
fn exit_PrimitiveLitNull(&mut self, _ctx: &PrimitiveLitNullContext<'input>) { }
/**
 * Enter a parse tree produced by {@link LibSLParser#arrayLitExpr}.
 * @param ctx the parse tree
 */
fn enter_arrayLitExpr(&mut self, _ctx: &ArrayLitExprContext<'input>) { }
/**
 * Exit a parse tree produced by {@link LibSLParser#arrayLitExpr}.
 * @param ctx the parse tree
 */
fn exit_arrayLitExpr(&mut self, _ctx: &ArrayLitExprContext<'input>) { }
/**
 * Enter a parse tree produced by {@link LibSLParser#setLitExpr}.
 * @param ctx the parse tree
 */
fn enter_setLitExpr(&mut self, _ctx: &SetLitExprContext<'input>) { }
/**
 * Exit a parse tree produced by {@link LibSLParser#setLitExpr}.
 * @param ctx the parse tree
 */
fn exit_setLitExpr(&mut self, _ctx: &SetLitExprContext<'input>) { }
/**
 * Enter a parse tree produced by {@link LibSLParser#actionCallExpr}.
 * @param ctx the parse tree
 */
fn enter_actionCallExpr(&mut self, _ctx: &ActionCallExprContext<'input>) { }
/**
 * Exit a parse tree produced by {@link LibSLParser#actionCallExpr}.
 * @param ctx the parse tree
 */
fn exit_actionCallExpr(&mut self, _ctx: &ActionCallExprContext<'input>) { }
/**
 * Enter a parse tree produced by {@link LibSLParser#instantiationExpr}.
 * @param ctx the parse tree
 */
fn enter_instantiationExpr(&mut self, _ctx: &InstantiationExprContext<'input>) { }
/**
 * Exit a parse tree produced by {@link LibSLParser#instantiationExpr}.
 * @param ctx the parse tree
 */
fn exit_instantiationExpr(&mut self, _ctx: &InstantiationExprContext<'input>) { }
/**
 * Enter a parse tree produced by {@link LibSLParser#constructorArgList}.
 * @param ctx the parse tree
 */
fn enter_constructorArgList(&mut self, _ctx: &ConstructorArgListContext<'input>) { }
/**
 * Exit a parse tree produced by {@link LibSLParser#constructorArgList}.
 * @param ctx the parse tree
 */
fn exit_constructorArgList(&mut self, _ctx: &ConstructorArgListContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code ConstructorArgState}
 * labeled alternative in {@link LibSLParser#constructorArg}.
 * @param ctx the parse tree
 */
fn enter_ConstructorArgState(&mut self, _ctx: &ConstructorArgStateContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code ConstructorArgState}
 * labeled alternative in {@link LibSLParser#constructorArg}.
 * @param ctx the parse tree
 */
fn exit_ConstructorArgState(&mut self, _ctx: &ConstructorArgStateContext<'input>) { }
/**
 * Enter a parse tree produced by the {@code ConstructorArgVar}
 * labeled alternative in {@link LibSLParser#constructorArg}.
 * @param ctx the parse tree
 */
fn enter_ConstructorArgVar(&mut self, _ctx: &ConstructorArgVarContext<'input>) { }
/**
 * Exit a parse tree produced by the {@code ConstructorArgVar}
 * labeled alternative in {@link LibSLParser#constructorArg}.
 * @param ctx the parse tree
 */
fn exit_ConstructorArgVar(&mut self, _ctx: &ConstructorArgVarContext<'input>) { }
/**
 * Enter a parse tree produced by {@link LibSLParser#ident}.
 * @param ctx the parse tree
 */
fn enter_ident(&mut self, _ctx: &IdentContext<'input>) { }
/**
 * Exit a parse tree produced by {@link LibSLParser#ident}.
 * @param ctx the parse tree
 */
fn exit_ident(&mut self, _ctx: &IdentContext<'input>) { }

}

antlr_rust::coerce_from!{ 'input : LibSLParserListener<'input> }


