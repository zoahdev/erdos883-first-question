import Erdos883AdaptiveCertificate2737Data
import Erdos883AdaptiveSpanCompactCore
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
def adaptiveNumericSpans2737_0Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 11 33744519360558710026383982201694397289137047180323957498581704916295478157909837045899065211985510759106106262707499350825976085229183836697241469343433955404685076915495418129706306415521788236122460035766305821964324204359788249307142458375240761242191586241612129284227350777333684148447021060522644346165324506611965663117440
def adaptiveNumericSpans2737_0 : List AdaptiveNumericSpan := [adaptiveNumericSpans2737_0Chunk0].flatten
def adaptiveSpanEven2737_0 := adaptiveSpanTreeOfSpans (coreEvenSpans 1369 0 adaptiveNumericSpans2737_0)
def adaptiveSpanWhole2737_0 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans2737_0)
theorem adaptiveSpanNumericCheck2737_0 : coreNumericSpansCheck 2671 7 480 1155 adaptiveNumericSpans2737_0 adaptiveRows2737 = true := by decide +kernel
theorem adaptiveSpanEvenCache2737_0 : adaptiveSpanEven2737_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain2737_0 : adaptiveSpanEven2737_0.domainCheck 1369 = true := by decide +kernel
theorem adaptiveSpanEvenEntries2737_0 : adaptiveSpanEven2737_0.spans = coreEvenSpans 1369 0 adaptiveNumericSpans2737_0 := by decide +kernel
theorem adaptiveSpanWholeCache2737_0 : adaptiveSpanWhole2737_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain2737_0 : adaptiveSpanWhole2737_0.domainCheck 1369 = true := by decide +kernel
theorem adaptiveSpanWholeEntries2737_0 : adaptiveSpanWhole2737_0.spans = coreWholeSpans 0 adaptiveNumericSpans2737_0 := by decide +kernel
def adaptiveNumericSpans2737_1Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 11 33744519360558710026383982201694397289137047180323957498581704916295478157909837045899065211985510759106106262707499350825976085229183836697241469343433955404685076915495418129706306415521788236122460035766305821964324204359788249307142458375240761242191586241612129284227485637005586418709116323461995984066070505857318821822592
def adaptiveNumericSpans2737_1 : List AdaptiveNumericSpan := [adaptiveNumericSpans2737_1Chunk0].flatten
def adaptiveSpanEven2737_1 := adaptiveSpanTreeOfSpans (coreEvenSpans 1369 0 adaptiveNumericSpans2737_1)
def adaptiveSpanWhole2737_1 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans2737_1)
theorem adaptiveSpanNumericCheck2737_1 : coreNumericSpansCheck 2671 7 240 385 adaptiveNumericSpans2737_1 adaptiveRows2737 = true := by decide +kernel
theorem adaptiveSpanEvenCache2737_1 : adaptiveSpanEven2737_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain2737_1 : adaptiveSpanEven2737_1.domainCheck 1369 = true := by decide +kernel
theorem adaptiveSpanEvenEntries2737_1 : adaptiveSpanEven2737_1.spans = coreEvenSpans 1369 0 adaptiveNumericSpans2737_1 := by decide +kernel
theorem adaptiveSpanWholeCache2737_1 : adaptiveSpanWhole2737_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain2737_1 : adaptiveSpanWhole2737_1.domainCheck 1369 = true := by decide +kernel
theorem adaptiveSpanWholeEntries2737_1 : adaptiveSpanWhole2737_1.spans = coreWholeSpans 0 adaptiveNumericSpans2737_1 := by decide +kernel
end Erdos883Verified
