import Erdos883AdaptiveCertificate1333Data
import Erdos883AdaptiveSpanCompactCore
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
def adaptiveNumericSpans1333_2Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 6 5053457110307285872305799122556346088379216622135734718119510873114708754846382831868546064954690877172437614540971308124309551274961107555080310225370972635811855611673914114176
def adaptiveNumericSpans1333_2 : List AdaptiveNumericSpan := [adaptiveNumericSpans1333_2Chunk0].flatten
def adaptiveSpanEven1333_2 := adaptiveSpanTreeOfSpans (coreEvenSpans 667 0 adaptiveNumericSpans1333_2)
def adaptiveSpanWhole1333_2 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans1333_2)
theorem adaptiveSpanNumericCheck1333_2 : coreNumericSpansCheck 1311 6 720 1001 adaptiveNumericSpans1333_2 adaptiveRows1333 = true := by decide +kernel
theorem adaptiveSpanEvenCache1333_2 : adaptiveSpanEven1333_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain1333_2 : adaptiveSpanEven1333_2.domainCheck 667 = true := by decide +kernel
theorem adaptiveSpanEvenEntries1333_2 : adaptiveSpanEven1333_2.spans = coreEvenSpans 667 0 adaptiveNumericSpans1333_2 := by decide +kernel
theorem adaptiveSpanWholeCache1333_2 : adaptiveSpanWhole1333_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain1333_2 : adaptiveSpanWhole1333_2.domainCheck 667 = true := by decide +kernel
theorem adaptiveSpanWholeEntries1333_2 : adaptiveSpanWhole1333_2.spans = coreWholeSpans 0 adaptiveNumericSpans1333_2 := by decide +kernel
end Erdos883Verified
