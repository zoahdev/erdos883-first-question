import Erdos883AdaptiveSpan30284Level6TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength30284_6 : adaptiveNumericSpans30284_6.length = 473 := by decide +kernel
theorem adaptiveSpanEvenCache30284_6 : adaptiveSpanEven30284_6.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain30284_6 : adaptiveSpanEven30284_6.domainCheck 15142 = true := by decide +kernel
theorem adaptiveSpanEvenEntries30284_6 : adaptiveSpanEven30284_6.spans = coreEvenSpans 15142 0 adaptiveNumericSpans30284_6 := by
  decide +kernel
theorem adaptiveSpanWholeCache30284_6 : adaptiveSpanWhole30284_6.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain30284_6 : adaptiveSpanWhole30284_6.domainCheck 15142 = true := by decide +kernel
theorem adaptiveSpanWholeEntries30284_6 : adaptiveSpanWhole30284_6.spans = coreWholeSpans 0 adaptiveNumericSpans30284_6 := by
  decide +kernel
end Erdos883Verified
