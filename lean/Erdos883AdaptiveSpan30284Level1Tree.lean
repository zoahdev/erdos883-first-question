import Erdos883AdaptiveSpan30284Level1TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength30284_1 : adaptiveNumericSpans30284_1.length = 473 := by decide +kernel
theorem adaptiveSpanEvenCache30284_1 : adaptiveSpanEven30284_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain30284_1 : adaptiveSpanEven30284_1.domainCheck 15142 = true := by decide +kernel
theorem adaptiveSpanEvenEntries30284_1 : adaptiveSpanEven30284_1.spans = coreEvenSpans 15142 0 adaptiveNumericSpans30284_1 := by
  decide +kernel
theorem adaptiveSpanWholeCache30284_1 : adaptiveSpanWhole30284_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain30284_1 : adaptiveSpanWhole30284_1.domainCheck 15142 = true := by decide +kernel
theorem adaptiveSpanWholeEntries30284_1 : adaptiveSpanWhole30284_1.spans = coreWholeSpans 0 adaptiveNumericSpans30284_1 := by
  decide +kernel
end Erdos883Verified
