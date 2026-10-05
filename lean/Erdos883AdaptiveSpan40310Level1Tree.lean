import Erdos883AdaptiveSpan40310Level1TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength40310_1 : adaptiveNumericSpans40310_1.length = 507 := by decide +kernel
theorem adaptiveSpanEvenCache40310_1 : adaptiveSpanEven40310_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain40310_1 : adaptiveSpanEven40310_1.domainCheck 20155 = true := by decide +kernel
theorem adaptiveSpanEvenEntries40310_1 : adaptiveSpanEven40310_1.spans = coreEvenSpans 20155 0 adaptiveNumericSpans40310_1 := by
  decide +kernel
theorem adaptiveSpanWholeCache40310_1 : adaptiveSpanWhole40310_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain40310_1 : adaptiveSpanWhole40310_1.domainCheck 20155 = true := by decide +kernel
theorem adaptiveSpanWholeEntries40310_1 : adaptiveSpanWhole40310_1.spans = coreWholeSpans 0 adaptiveNumericSpans40310_1 := by
  decide +kernel
end Erdos883Verified
