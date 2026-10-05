import Erdos883AdaptiveSpan40310Level2TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength40310_2 : adaptiveNumericSpans40310_2.length = 507 := by decide +kernel
theorem adaptiveSpanEvenCache40310_2 : adaptiveSpanEven40310_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain40310_2 : adaptiveSpanEven40310_2.domainCheck 20155 = true := by decide +kernel
theorem adaptiveSpanEvenEntries40310_2 : adaptiveSpanEven40310_2.spans = coreEvenSpans 20155 0 adaptiveNumericSpans40310_2 := by
  decide +kernel
theorem adaptiveSpanWholeCache40310_2 : adaptiveSpanWhole40310_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain40310_2 : adaptiveSpanWhole40310_2.domainCheck 20155 = true := by decide +kernel
theorem adaptiveSpanWholeEntries40310_2 : adaptiveSpanWhole40310_2.spans = coreWholeSpans 0 adaptiveNumericSpans40310_2 := by
  decide +kernel
end Erdos883Verified
