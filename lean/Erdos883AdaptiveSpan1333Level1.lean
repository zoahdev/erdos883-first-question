import Erdos883AdaptiveCertificate1333Data
import Erdos883AdaptiveSpanCompactCore
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
def adaptiveNumericSpans1333_1Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 6 5053457110307285872305799122556346088379216622135734718119510873114708754846382831868546064954690877172437614540971308124222198986748204407557699816916481999400783991850542301312
def adaptiveNumericSpans1333_1 : List AdaptiveNumericSpan := [adaptiveNumericSpans1333_1Chunk0].flatten
def adaptiveSpanEven1333_1 := adaptiveSpanTreeOfSpans (coreEvenSpans 667 0 adaptiveNumericSpans1333_1)
def adaptiveSpanWhole1333_1 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans1333_1)
theorem adaptiveSpanNumericCheck1333_1 : coreNumericSpansCheck 1311 6 240 385 adaptiveNumericSpans1333_1 adaptiveRows1333 = true := by decide +kernel
theorem adaptiveSpanEvenCache1333_1 : adaptiveSpanEven1333_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain1333_1 : adaptiveSpanEven1333_1.domainCheck 667 = true := by decide +kernel
theorem adaptiveSpanEvenEntries1333_1 : adaptiveSpanEven1333_1.spans = coreEvenSpans 667 0 adaptiveNumericSpans1333_1 := by decide +kernel
theorem adaptiveSpanWholeCache1333_1 : adaptiveSpanWhole1333_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain1333_1 : adaptiveSpanWhole1333_1.domainCheck 667 = true := by decide +kernel
theorem adaptiveSpanWholeEntries1333_1 : adaptiveSpanWhole1333_1.spans = coreWholeSpans 0 adaptiveNumericSpans1333_1 := by decide +kernel
end Erdos883Verified
