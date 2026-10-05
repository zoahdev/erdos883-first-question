import Erdos883AdaptiveCertificate2737Data
import Erdos883AdaptiveSpanCompactCore
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
def adaptiveNumericSpans2737_2Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 11 33744519360558710026383982201694397289137047180323957498581704916295478157909837045899065211985510759106106262707499350825976085229183836697241469343433955404685076915495418129706306415521788236122460035766305822200736354268199097724811637671396439659800579281623243825536664505638101946662466417762135671216159727136535016898688
def adaptiveNumericSpans2737_2 : List AdaptiveNumericSpan := [adaptiveNumericSpans2737_2Chunk0].flatten
def adaptiveSpanEven2737_2 := adaptiveSpanTreeOfSpans (coreEvenSpans 1369 0 adaptiveNumericSpans2737_2)
def adaptiveSpanWhole2737_2 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans2737_2)
theorem adaptiveSpanNumericCheck2737_2 : coreNumericSpansCheck 2671 7 720 1001 adaptiveNumericSpans2737_2 adaptiveRows2737 = true := by decide +kernel
theorem adaptiveSpanEvenCache2737_2 : adaptiveSpanEven2737_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain2737_2 : adaptiveSpanEven2737_2.domainCheck 1369 = true := by decide +kernel
theorem adaptiveSpanEvenEntries2737_2 : adaptiveSpanEven2737_2.spans = coreEvenSpans 1369 0 adaptiveNumericSpans2737_2 := by decide +kernel
theorem adaptiveSpanWholeCache2737_2 : adaptiveSpanWhole2737_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain2737_2 : adaptiveSpanWhole2737_2.domainCheck 1369 = true := by decide +kernel
theorem adaptiveSpanWholeEntries2737_2 : adaptiveSpanWhole2737_2.spans = coreWholeSpans 0 adaptiveNumericSpans2737_2 := by decide +kernel
def adaptiveNumericSpans2737_3Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 11 33744519360558710026383982201694397289137047180323957498581704916295478157909837045899065211985510759106106262707499350825976085229183836697241469343433955404685076915495418129706306730818540674608411145598810533136679644960036371185757435011142515845130910198416174153339679601880838824110911663704133147070272832519304023900288
def adaptiveNumericSpans2737_3 : List AdaptiveNumericSpan := [adaptiveNumericSpans2737_3Chunk0].flatten
def adaptiveSpanEven2737_3 := adaptiveSpanTreeOfSpans (coreEvenSpans 1369 0 adaptiveNumericSpans2737_3)
def adaptiveSpanWhole2737_3 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans2737_3)
theorem adaptiveSpanNumericCheck2737_3 : coreNumericSpansCheck 2671 7 1920 2431 adaptiveNumericSpans2737_3 adaptiveRows2737 = true := by decide +kernel
theorem adaptiveSpanEvenCache2737_3 : adaptiveSpanEven2737_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain2737_3 : adaptiveSpanEven2737_3.domainCheck 1369 = true := by decide +kernel
theorem adaptiveSpanEvenEntries2737_3 : adaptiveSpanEven2737_3.spans = coreEvenSpans 1369 0 adaptiveNumericSpans2737_3 := by decide +kernel
theorem adaptiveSpanWholeCache2737_3 : adaptiveSpanWhole2737_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain2737_3 : adaptiveSpanWhole2737_3.domainCheck 1369 = true := by decide +kernel
theorem adaptiveSpanWholeEntries2737_3 : adaptiveSpanWhole2737_3.spans = coreWholeSpans 0 adaptiveNumericSpans2737_3 := by decide +kernel
end Erdos883Verified
