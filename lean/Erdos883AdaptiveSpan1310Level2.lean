import Erdos883AdaptiveCertificate1310Data
import Erdos883AdaptiveSpanCompactCore
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
def adaptiveNumericSpans1310_2Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 6 4958482190854302176242960091858710017571000044744310590082802327501023023132092727096276224523907081427791121457599820444326232472320599250845184025613869279878115167070242996352
def adaptiveNumericSpans1310_2 : List AdaptiveNumericSpan := [adaptiveNumericSpans1310_2Chunk0].flatten
def adaptiveSpanEven1310_2 := adaptiveSpanTreeOfSpans (coreEvenSpans 655 0 adaptiveNumericSpans1310_2)
def adaptiveSpanWhole1310_2 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans1310_2)
theorem adaptiveSpanNumericCheck1310_2 : coreNumericSpansCheck 1287 6 720 1001 adaptiveNumericSpans1310_2 adaptiveRows1310 = true := by decide +kernel
theorem adaptiveSpanEvenCache1310_2 : adaptiveSpanEven1310_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain1310_2 : adaptiveSpanEven1310_2.domainCheck 655 = true := by decide +kernel
theorem adaptiveSpanEvenEntries1310_2 : adaptiveSpanEven1310_2.spans = coreEvenSpans 655 0 adaptiveNumericSpans1310_2 := by decide +kernel
theorem adaptiveSpanWholeCache1310_2 : adaptiveSpanWhole1310_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain1310_2 : adaptiveSpanWhole1310_2.domainCheck 655 = true := by decide +kernel
theorem adaptiveSpanWholeEntries1310_2 : adaptiveSpanWhole1310_2.spans = coreWholeSpans 0 adaptiveNumericSpans1310_2 := by decide +kernel
end Erdos883Verified
