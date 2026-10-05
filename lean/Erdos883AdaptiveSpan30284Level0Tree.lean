import Erdos883AdaptiveSpan30284Level0TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength30284_0 : adaptiveNumericSpans30284_0.length = 473 := by decide +kernel
theorem adaptiveSpanEvenCache30284_0 : adaptiveSpanEven30284_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain30284_0 : adaptiveSpanEven30284_0.domainCheck 15142 = true := by decide +kernel
theorem adaptiveSpanEvenEntries30284_0 : adaptiveSpanEven30284_0.spans = coreEvenSpans 15142 0 adaptiveNumericSpans30284_0 := by
  decide +kernel
theorem adaptiveSpanWholeCache30284_0 : adaptiveSpanWhole30284_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain30284_0 : adaptiveSpanWhole30284_0.domainCheck 15142 = true := by decide +kernel
theorem adaptiveSpanWholeEntries30284_0 : adaptiveSpanWhole30284_0.spans = coreWholeSpans 0 adaptiveNumericSpans30284_0 := by
  decide +kernel
end Erdos883Verified
