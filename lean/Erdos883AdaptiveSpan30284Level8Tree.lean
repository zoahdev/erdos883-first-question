import Erdos883AdaptiveSpan30284Level8TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength30284_8 : adaptiveNumericSpans30284_8.length = 473 := by decide +kernel
theorem adaptiveSpanEvenCache30284_8 : adaptiveSpanEven30284_8.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain30284_8 : adaptiveSpanEven30284_8.domainCheck 15142 = true := by decide +kernel
theorem adaptiveSpanEvenEntries30284_8 : adaptiveSpanEven30284_8.spans = coreEvenSpans 15142 0 adaptiveNumericSpans30284_8 := by
  decide +kernel
theorem adaptiveSpanWholeCache30284_8 : adaptiveSpanWhole30284_8.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain30284_8 : adaptiveSpanWhole30284_8.domainCheck 15142 = true := by decide +kernel
theorem adaptiveSpanWholeEntries30284_8 : adaptiveSpanWhole30284_8.spans = coreWholeSpans 0 adaptiveNumericSpans30284_8 := by
  decide +kernel
end Erdos883Verified
