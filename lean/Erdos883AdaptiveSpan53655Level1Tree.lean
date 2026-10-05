import Erdos883AdaptiveSpan53655Level1TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength53655_1 : adaptiveNumericSpans53655_1.length = 538 := by decide +kernel
theorem adaptiveSpanEvenCache53655_1 : adaptiveSpanEven53655_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain53655_1 : adaptiveSpanEven53655_1.domainCheck 26828 = true := by decide +kernel
theorem adaptiveSpanEvenEntries53655_1 : adaptiveSpanEven53655_1.spans = coreEvenSpans 26828 0 adaptiveNumericSpans53655_1 := by
  decide +kernel
theorem adaptiveSpanWholeCache53655_1 : adaptiveSpanWhole53655_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain53655_1 : adaptiveSpanWhole53655_1.domainCheck 26828 = true := by decide +kernel
theorem adaptiveSpanWholeEntries53655_1 : adaptiveSpanWhole53655_1.spans = coreWholeSpans 0 adaptiveNumericSpans53655_1 := by
  decide +kernel
end Erdos883Verified
