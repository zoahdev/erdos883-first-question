import Erdos883AdaptiveSpan14124Level2TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength14124_2 : adaptiveNumericSpans14124_2.length = 391 := by decide +kernel
theorem adaptiveSpanEvenCache14124_2 : adaptiveSpanEven14124_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain14124_2 : adaptiveSpanEven14124_2.domainCheck 7062 = true := by decide +kernel
theorem adaptiveSpanEvenEntries14124_2 : adaptiveSpanEven14124_2.spans = coreEvenSpans 7062 0 adaptiveNumericSpans14124_2 := by
  decide +kernel
theorem adaptiveSpanWholeCache14124_2 : adaptiveSpanWhole14124_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain14124_2 : adaptiveSpanWhole14124_2.domainCheck 7062 = true := by decide +kernel
theorem adaptiveSpanWholeEntries14124_2 : adaptiveSpanWhole14124_2.spans = coreWholeSpans 0 adaptiveNumericSpans14124_2 := by
  decide +kernel
end Erdos883Verified
