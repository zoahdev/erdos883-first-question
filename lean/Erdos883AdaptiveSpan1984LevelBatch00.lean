import Erdos883AdaptiveCertificate1984Data
import Erdos883AdaptiveSpanCompactCore
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
def adaptiveNumericSpans1984_0Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 8 12088681585964133632017459050147822105316074537225062711620603457900810465061357447012580106257667674178758608208012884759414056335612567016196893560932843088525575224772500558359106481591169743613396094099182145740520401941380958158585984
def adaptiveNumericSpans1984_0 : List AdaptiveNumericSpan := [adaptiveNumericSpans1984_0Chunk0].flatten
def adaptiveSpanEven1984_0 := adaptiveSpanTreeOfSpans (coreEvenSpans 992 0 adaptiveNumericSpans1984_0)
def adaptiveSpanWhole1984_0 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans1984_0)
theorem adaptiveSpanNumericCheck1984_0 : coreNumericSpansCheck 1936 6 480 1155 adaptiveNumericSpans1984_0 adaptiveRows1984 = true := by decide +kernel
theorem adaptiveSpanEvenCache1984_0 : adaptiveSpanEven1984_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain1984_0 : adaptiveSpanEven1984_0.domainCheck 992 = true := by decide +kernel
theorem adaptiveSpanEvenEntries1984_0 : adaptiveSpanEven1984_0.spans = coreEvenSpans 992 0 adaptiveNumericSpans1984_0 := by decide +kernel
theorem adaptiveSpanWholeCache1984_0 : adaptiveSpanWhole1984_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain1984_0 : adaptiveSpanWhole1984_0.domainCheck 992 = true := by decide +kernel
theorem adaptiveSpanWholeEntries1984_0 : adaptiveSpanWhole1984_0.spans = coreWholeSpans 0 adaptiveNumericSpans1984_0 := by decide +kernel
def adaptiveNumericSpans1984_1Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 8 12088681585964133632017459050147822105316074537225062711620603457900810465061357447012580106257667674178758608208012884759414056335612567016196893560932843088525575224772500558359106521436072805647791713154141499753275195275981616599531648
def adaptiveNumericSpans1984_1 : List AdaptiveNumericSpan := [adaptiveNumericSpans1984_1Chunk0].flatten
def adaptiveSpanEven1984_1 := adaptiveSpanTreeOfSpans (coreEvenSpans 992 0 adaptiveNumericSpans1984_1)
def adaptiveSpanWhole1984_1 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans1984_1)
theorem adaptiveSpanNumericCheck1984_1 : coreNumericSpansCheck 1936 6 240 385 adaptiveNumericSpans1984_1 adaptiveRows1984 = true := by decide +kernel
theorem adaptiveSpanEvenCache1984_1 : adaptiveSpanEven1984_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain1984_1 : adaptiveSpanEven1984_1.domainCheck 992 = true := by decide +kernel
theorem adaptiveSpanEvenEntries1984_1 : adaptiveSpanEven1984_1.spans = coreEvenSpans 992 0 adaptiveNumericSpans1984_1 := by decide +kernel
theorem adaptiveSpanWholeCache1984_1 : adaptiveSpanWhole1984_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain1984_1 : adaptiveSpanWhole1984_1.domainCheck 992 = true := by decide +kernel
theorem adaptiveSpanWholeEntries1984_1 : adaptiveSpanWhole1984_1.spans = coreWholeSpans 0 adaptiveNumericSpans1984_1 := by decide +kernel
def adaptiveNumericSpans1984_2Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 8 12088681585964133632017459050147822105316074537225062711620603457900810465061357447012580106257667674178758608208012884759414056335612567016196893560932981018081766821509432909591690914522892066002438273171195541574810914746810081906524288
def adaptiveNumericSpans1984_2 : List AdaptiveNumericSpan := [adaptiveNumericSpans1984_2Chunk0].flatten
def adaptiveSpanEven1984_2 := adaptiveSpanTreeOfSpans (coreEvenSpans 992 0 adaptiveNumericSpans1984_2)
def adaptiveSpanWhole1984_2 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans1984_2)
theorem adaptiveSpanNumericCheck1984_2 : coreNumericSpansCheck 1936 6 720 1001 adaptiveNumericSpans1984_2 adaptiveRows1984 = true := by decide +kernel
theorem adaptiveSpanEvenCache1984_2 : adaptiveSpanEven1984_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain1984_2 : adaptiveSpanEven1984_2.domainCheck 992 = true := by decide +kernel
theorem adaptiveSpanEvenEntries1984_2 : adaptiveSpanEven1984_2.spans = coreEvenSpans 992 0 adaptiveNumericSpans1984_2 := by decide +kernel
theorem adaptiveSpanWholeCache1984_2 : adaptiveSpanWhole1984_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain1984_2 : adaptiveSpanWhole1984_2.domainCheck 992 = true := by decide +kernel
theorem adaptiveSpanWholeEntries1984_2 : adaptiveSpanWhole1984_2.spans = coreWholeSpans 0 adaptiveNumericSpans1984_2 := by decide +kernel
def adaptiveNumericSpans1984_3Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 8 12088681585964133632017459050147822105316074537225062711620603457900810465061357447012580106257667674178758608208012884759657856366379886995014531516026948639119607693246860456161105003785519964675635645168596473168105306929371971892281472
def adaptiveNumericSpans1984_3 : List AdaptiveNumericSpan := [adaptiveNumericSpans1984_3Chunk0].flatten
def adaptiveSpanEven1984_3 := adaptiveSpanTreeOfSpans (coreEvenSpans 992 0 adaptiveNumericSpans1984_3)
def adaptiveSpanWhole1984_3 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans1984_3)
theorem adaptiveSpanNumericCheck1984_3 : coreNumericSpansCheck 1936 6 120 143 adaptiveNumericSpans1984_3 adaptiveRows1984 = true := by decide +kernel
theorem adaptiveSpanEvenCache1984_3 : adaptiveSpanEven1984_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain1984_3 : adaptiveSpanEven1984_3.domainCheck 992 = true := by decide +kernel
theorem adaptiveSpanEvenEntries1984_3 : adaptiveSpanEven1984_3.spans = coreEvenSpans 992 0 adaptiveNumericSpans1984_3 := by decide +kernel
theorem adaptiveSpanWholeCache1984_3 : adaptiveSpanWhole1984_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain1984_3 : adaptiveSpanWhole1984_3.domainCheck 992 = true := by decide +kernel
theorem adaptiveSpanWholeEntries1984_3 : adaptiveSpanWhole1984_3.spans = coreWholeSpans 0 adaptiveNumericSpans1984_3 := by decide +kernel
def adaptiveNumericSpans1984_4Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 13 39570976765342031792378655425851287888367031194732295110069107147023991365023312422886986552831909788798563477070348804768905192231461890674806839919146849445943485279233510602322849327342710753759625637478744926558904108227822523744178666412608905586490619157510239731138133607067351146837260639900096307920819155294911710975904276784583672496102220775155925801375738532422481486683308160
def adaptiveNumericSpans1984_4 : List AdaptiveNumericSpan := [adaptiveNumericSpans1984_4Chunk0].flatten
def adaptiveSpanEven1984_4 := adaptiveSpanTreeOfSpans (coreEvenSpans 992 0 adaptiveNumericSpans1984_4)
def adaptiveSpanWhole1984_4 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans1984_4)
theorem adaptiveSpanNumericCheck1984_4 : coreNumericSpansCheck 1936 6 192 221 adaptiveNumericSpans1984_4 adaptiveRows1984 = true := by decide +kernel
theorem adaptiveSpanEvenCache1984_4 : adaptiveSpanEven1984_4.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain1984_4 : adaptiveSpanEven1984_4.domainCheck 992 = true := by decide +kernel
theorem adaptiveSpanEvenEntries1984_4 : adaptiveSpanEven1984_4.spans = coreEvenSpans 992 0 adaptiveNumericSpans1984_4 := by decide +kernel
theorem adaptiveSpanWholeCache1984_4 : adaptiveSpanWhole1984_4.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain1984_4 : adaptiveSpanWhole1984_4.domainCheck 992 = true := by decide +kernel
theorem adaptiveSpanWholeEntries1984_4 : adaptiveSpanWhole1984_4.spans = coreWholeSpans 0 adaptiveNumericSpans1984_4 := by decide +kernel
def adaptiveNumericSpans1984_5Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 14 50162172448203146150621838453075784871743616141607022121027906641500066088433221741529792191873325222740090327364007912203872587865536133931701005149837447313561117769983788109042913287512358579619551901854327861421297356903753643176476537386607580074713511177376929958195208240601949836417862675896547091420784403978906583915461051240348860069480846121587902962387334413252716799474372103152624387475302437436671393920
def adaptiveNumericSpans1984_5 : List AdaptiveNumericSpan := [adaptiveNumericSpans1984_5Chunk0].flatten
def adaptiveSpanEven1984_5 := adaptiveSpanTreeOfSpans (coreEvenSpans 992 0 adaptiveNumericSpans1984_5)
def adaptiveSpanWhole1984_5 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans1984_5)
theorem adaptiveSpanNumericCheck1984_5 : coreNumericSpansCheck 1936 6 288 323 adaptiveNumericSpans1984_5 adaptiveRows1984 = true := by decide +kernel
theorem adaptiveSpanEvenCache1984_5 : adaptiveSpanEven1984_5.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain1984_5 : adaptiveSpanEven1984_5.domainCheck 992 = true := by decide +kernel
theorem adaptiveSpanEvenEntries1984_5 : adaptiveSpanEven1984_5.spans = coreEvenSpans 992 0 adaptiveNumericSpans1984_5 := by decide +kernel
theorem adaptiveSpanWholeCache1984_5 : adaptiveSpanWhole1984_5.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain1984_5 : adaptiveSpanWhole1984_5.domainCheck 992 = true := by decide +kernel
theorem adaptiveSpanWholeEntries1984_5 : adaptiveSpanWhole1984_5.spans = coreWholeSpans 0 adaptiveNumericSpans1984_5 := by decide +kernel
end Erdos883Verified
