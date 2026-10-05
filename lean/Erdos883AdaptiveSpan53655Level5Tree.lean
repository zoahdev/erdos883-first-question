import Erdos883AdaptiveSpan53655Level5TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength53655_5 : adaptiveNumericSpans53655_5.length = 538 := by decide +kernel
theorem adaptiveSpanEvenCache53655_5 : adaptiveSpanEven53655_5.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain53655_5 : adaptiveSpanEven53655_5.domainCheck 26828 = true := by decide +kernel
theorem adaptiveSpanEvenEntries53655_5 : adaptiveSpanEven53655_5.spans = coreEvenSpans 26828 0 adaptiveNumericSpans53655_5 := by
  decide +kernel
theorem adaptiveSpanWholeCache53655_5 : adaptiveSpanWhole53655_5.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain53655_5 : adaptiveSpanWhole53655_5.domainCheck 26828 = true := by decide +kernel
theorem adaptiveSpanWholeEntries53655_5 : adaptiveSpanWhole53655_5.spans = coreWholeSpans 0 adaptiveNumericSpans53655_5 := by
  decide +kernel
end Erdos883Verified
