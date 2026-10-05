import Erdos883AdaptiveSpan30284Level4TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength30284_4 : adaptiveNumericSpans30284_4.length = 473 := by decide +kernel
theorem adaptiveSpanEvenCache30284_4 : adaptiveSpanEven30284_4.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain30284_4 : adaptiveSpanEven30284_4.domainCheck 15142 = true := by decide +kernel
theorem adaptiveSpanEvenEntries30284_4 : adaptiveSpanEven30284_4.spans = coreEvenSpans 15142 0 adaptiveNumericSpans30284_4 := by
  decide +kernel
theorem adaptiveSpanWholeCache30284_4 : adaptiveSpanWhole30284_4.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain30284_4 : adaptiveSpanWhole30284_4.domainCheck 15142 = true := by decide +kernel
theorem adaptiveSpanWholeEntries30284_4 : adaptiveSpanWhole30284_4.spans = coreWholeSpans 0 adaptiveNumericSpans30284_4 := by
  decide +kernel
end Erdos883Verified
