import Erdos883AdaptiveSpan30284Level3TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength30284_3 : adaptiveNumericSpans30284_3.length = 473 := by decide +kernel
theorem adaptiveSpanEvenCache30284_3 : adaptiveSpanEven30284_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain30284_3 : adaptiveSpanEven30284_3.domainCheck 15142 = true := by decide +kernel
theorem adaptiveSpanEvenEntries30284_3 : adaptiveSpanEven30284_3.spans = coreEvenSpans 15142 0 adaptiveNumericSpans30284_3 := by
  decide +kernel
theorem adaptiveSpanWholeCache30284_3 : adaptiveSpanWhole30284_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain30284_3 : adaptiveSpanWhole30284_3.domainCheck 15142 = true := by decide +kernel
theorem adaptiveSpanWholeEntries30284_3 : adaptiveSpanWhole30284_3.spans = coreWholeSpans 0 adaptiveNumericSpans30284_3 := by
  decide +kernel
end Erdos883Verified
