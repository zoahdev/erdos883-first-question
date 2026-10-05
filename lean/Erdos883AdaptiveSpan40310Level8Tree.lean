import Erdos883AdaptiveSpan40310Level8TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength40310_8 : adaptiveNumericSpans40310_8.length = 507 := by decide +kernel
theorem adaptiveSpanEvenCache40310_8 : adaptiveSpanEven40310_8.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain40310_8 : adaptiveSpanEven40310_8.domainCheck 20155 = true := by decide +kernel
theorem adaptiveSpanEvenEntries40310_8 : adaptiveSpanEven40310_8.spans = coreEvenSpans 20155 0 adaptiveNumericSpans40310_8 := by
  decide +kernel
theorem adaptiveSpanWholeCache40310_8 : adaptiveSpanWhole40310_8.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain40310_8 : adaptiveSpanWhole40310_8.domainCheck 20155 = true := by decide +kernel
theorem adaptiveSpanWholeEntries40310_8 : adaptiveSpanWhole40310_8.spans = coreWholeSpans 0 adaptiveNumericSpans40310_8 := by
  decide +kernel
end Erdos883Verified
