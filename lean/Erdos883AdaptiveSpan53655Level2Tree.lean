import Erdos883AdaptiveSpan53655Level2TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength53655_2 : adaptiveNumericSpans53655_2.length = 538 := by decide +kernel
theorem adaptiveSpanEvenCache53655_2 : adaptiveSpanEven53655_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain53655_2 : adaptiveSpanEven53655_2.domainCheck 26828 = true := by decide +kernel
theorem adaptiveSpanEvenEntries53655_2 : adaptiveSpanEven53655_2.spans = coreEvenSpans 26828 0 adaptiveNumericSpans53655_2 := by
  decide +kernel
theorem adaptiveSpanWholeCache53655_2 : adaptiveSpanWhole53655_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain53655_2 : adaptiveSpanWhole53655_2.domainCheck 26828 = true := by decide +kernel
theorem adaptiveSpanWholeEntries53655_2 : adaptiveSpanWhole53655_2.spans = coreWholeSpans 0 adaptiveNumericSpans53655_2 := by
  decide +kernel
end Erdos883Verified
