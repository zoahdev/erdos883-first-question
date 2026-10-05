import Erdos883AdaptiveSpan30284Level7TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength30284_7 : adaptiveNumericSpans30284_7.length = 473 := by decide +kernel
theorem adaptiveSpanEvenCache30284_7 : adaptiveSpanEven30284_7.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain30284_7 : adaptiveSpanEven30284_7.domainCheck 15142 = true := by decide +kernel
theorem adaptiveSpanEvenEntries30284_7 : adaptiveSpanEven30284_7.spans = coreEvenSpans 15142 0 adaptiveNumericSpans30284_7 := by
  decide +kernel
theorem adaptiveSpanWholeCache30284_7 : adaptiveSpanWhole30284_7.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain30284_7 : adaptiveSpanWhole30284_7.domainCheck 15142 = true := by decide +kernel
theorem adaptiveSpanWholeEntries30284_7 : adaptiveSpanWhole30284_7.spans = coreWholeSpans 0 adaptiveNumericSpans30284_7 := by
  decide +kernel
end Erdos883Verified
