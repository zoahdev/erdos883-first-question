import Erdos883AdaptiveSpan40310Level0TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength40310_0 : adaptiveNumericSpans40310_0.length = 507 := by decide +kernel
theorem adaptiveSpanEvenCache40310_0 : adaptiveSpanEven40310_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain40310_0 : adaptiveSpanEven40310_0.domainCheck 20155 = true := by decide +kernel
theorem adaptiveSpanEvenEntries40310_0 : adaptiveSpanEven40310_0.spans = coreEvenSpans 20155 0 adaptiveNumericSpans40310_0 := by
  decide +kernel
theorem adaptiveSpanWholeCache40310_0 : adaptiveSpanWhole40310_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain40310_0 : adaptiveSpanWhole40310_0.domainCheck 20155 = true := by decide +kernel
theorem adaptiveSpanWholeEntries40310_0 : adaptiveSpanWhole40310_0.spans = coreWholeSpans 0 adaptiveNumericSpans40310_0 := by
  decide +kernel
end Erdos883Verified
