import Erdos883AdaptiveSpan30284Level5TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength30284_5 : adaptiveNumericSpans30284_5.length = 473 := by decide +kernel
theorem adaptiveSpanEvenCache30284_5 : adaptiveSpanEven30284_5.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain30284_5 : adaptiveSpanEven30284_5.domainCheck 15142 = true := by decide +kernel
theorem adaptiveSpanEvenEntries30284_5 : adaptiveSpanEven30284_5.spans = coreEvenSpans 15142 0 adaptiveNumericSpans30284_5 := by
  decide +kernel
theorem adaptiveSpanWholeCache30284_5 : adaptiveSpanWhole30284_5.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain30284_5 : adaptiveSpanWhole30284_5.domainCheck 15142 = true := by decide +kernel
theorem adaptiveSpanWholeEntries30284_5 : adaptiveSpanWhole30284_5.spans = coreWholeSpans 0 adaptiveNumericSpans30284_5 := by
  decide +kernel
end Erdos883Verified
