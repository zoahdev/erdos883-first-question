import Erdos883AdaptiveSpan14124Level4TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength14124_4 : adaptiveNumericSpans14124_4.length = 391 := by decide +kernel
theorem adaptiveSpanEvenCache14124_4 : adaptiveSpanEven14124_4.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain14124_4 : adaptiveSpanEven14124_4.domainCheck 7062 = true := by decide +kernel
theorem adaptiveSpanEvenEntries14124_4 : adaptiveSpanEven14124_4.spans = coreEvenSpans 7062 0 adaptiveNumericSpans14124_4 := by
  decide +kernel
theorem adaptiveSpanWholeCache14124_4 : adaptiveSpanWhole14124_4.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain14124_4 : adaptiveSpanWhole14124_4.domainCheck 7062 = true := by decide +kernel
theorem adaptiveSpanWholeEntries14124_4 : adaptiveSpanWhole14124_4.spans = coreWholeSpans 0 adaptiveNumericSpans14124_4 := by
  decide +kernel
end Erdos883Verified
