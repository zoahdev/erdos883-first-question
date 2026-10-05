import Erdos883AdaptiveSpan30284Level2TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength30284_2 : adaptiveNumericSpans30284_2.length = 473 := by decide +kernel
theorem adaptiveSpanEvenCache30284_2 : adaptiveSpanEven30284_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain30284_2 : adaptiveSpanEven30284_2.domainCheck 15142 = true := by decide +kernel
theorem adaptiveSpanEvenEntries30284_2 : adaptiveSpanEven30284_2.spans = coreEvenSpans 15142 0 adaptiveNumericSpans30284_2 := by
  decide +kernel
theorem adaptiveSpanWholeCache30284_2 : adaptiveSpanWhole30284_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain30284_2 : adaptiveSpanWhole30284_2.domainCheck 15142 = true := by decide +kernel
theorem adaptiveSpanWholeEntries30284_2 : adaptiveSpanWhole30284_2.spans = coreWholeSpans 0 adaptiveNumericSpans30284_2 := by
  decide +kernel
end Erdos883Verified
