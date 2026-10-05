import Erdos883AdaptiveSpan53655Level8TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength53655_8 : adaptiveNumericSpans53655_8.length = 538 := by decide +kernel
theorem adaptiveSpanEvenCache53655_8 : adaptiveSpanEven53655_8.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain53655_8 : adaptiveSpanEven53655_8.domainCheck 26828 = true := by decide +kernel
theorem adaptiveSpanEvenEntries53655_8 : adaptiveSpanEven53655_8.spans = coreEvenSpans 26828 0 adaptiveNumericSpans53655_8 := by
  decide +kernel
theorem adaptiveSpanWholeCache53655_8 : adaptiveSpanWhole53655_8.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain53655_8 : adaptiveSpanWhole53655_8.domainCheck 26828 = true := by decide +kernel
theorem adaptiveSpanWholeEntries53655_8 : adaptiveSpanWhole53655_8.spans = coreWholeSpans 0 adaptiveNumericSpans53655_8 := by
  decide +kernel
end Erdos883Verified
