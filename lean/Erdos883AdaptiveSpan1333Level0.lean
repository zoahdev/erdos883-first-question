import Erdos883AdaptiveCertificate1333Data
import Erdos883AdaptiveSpanCompactCore
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
def adaptiveNumericSpans1333_0Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 9 10294073938559252827755587967610878838915320854628547367402345238070489855626581939345414051054136709362847562254476488996646772197674668357953792822466632274418572697333730573955947692717701000107840669460530410750491360985435215892575481522361963417981032543949946944
def adaptiveNumericSpans1333_0 : List AdaptiveNumericSpan := [adaptiveNumericSpans1333_0Chunk0].flatten
def adaptiveSpanEven1333_0 := adaptiveSpanTreeOfSpans (coreEvenSpans 667 0 adaptiveNumericSpans1333_0)
def adaptiveSpanWhole1333_0 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans1333_0)
theorem adaptiveSpanNumericCheck1333_0 : coreNumericSpansCheck 1311 6 480 1155 adaptiveNumericSpans1333_0 adaptiveRows1333 = true := by decide +kernel
theorem adaptiveSpanEvenCache1333_0 : adaptiveSpanEven1333_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain1333_0 : adaptiveSpanEven1333_0.domainCheck 667 = true := by decide +kernel
theorem adaptiveSpanEvenEntries1333_0 : adaptiveSpanEven1333_0.spans = coreEvenSpans 667 0 adaptiveNumericSpans1333_0 := by decide +kernel
theorem adaptiveSpanWholeCache1333_0 : adaptiveSpanWhole1333_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain1333_0 : adaptiveSpanWhole1333_0.domainCheck 667 = true := by decide +kernel
theorem adaptiveSpanWholeEntries1333_0 : adaptiveSpanWhole1333_0.spans = coreWholeSpans 0 adaptiveNumericSpans1333_0 := by decide +kernel
end Erdos883Verified
