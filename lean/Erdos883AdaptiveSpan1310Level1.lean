import Erdos883AdaptiveCertificate1310Data
import Erdos883AdaptiveSpanCompactCore
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
def adaptiveNumericSpans1310_1Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 6 4958482190854302176242960091858710017571000044744310590082802327501023023132092727096276224523907081427791121457599820444241945178112431155701096147621050136192666679432278179968
def adaptiveNumericSpans1310_1 : List AdaptiveNumericSpan := [adaptiveNumericSpans1310_1Chunk0].flatten
def adaptiveSpanEven1310_1 := adaptiveSpanTreeOfSpans (coreEvenSpans 655 0 adaptiveNumericSpans1310_1)
def adaptiveSpanWhole1310_1 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans1310_1)
theorem adaptiveSpanNumericCheck1310_1 : coreNumericSpansCheck 1287 6 240 385 adaptiveNumericSpans1310_1 adaptiveRows1310 = true := by decide +kernel
theorem adaptiveSpanEvenCache1310_1 : adaptiveSpanEven1310_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain1310_1 : adaptiveSpanEven1310_1.domainCheck 655 = true := by decide +kernel
theorem adaptiveSpanEvenEntries1310_1 : adaptiveSpanEven1310_1.spans = coreEvenSpans 655 0 adaptiveNumericSpans1310_1 := by decide +kernel
theorem adaptiveSpanWholeCache1310_1 : adaptiveSpanWhole1310_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain1310_1 : adaptiveSpanWhole1310_1.domainCheck 655 = true := by decide +kernel
theorem adaptiveSpanWholeEntries1310_1 : adaptiveSpanWhole1310_1.spans = coreWholeSpans 0 adaptiveNumericSpans1310_1 := by decide +kernel
end Erdos883Verified
