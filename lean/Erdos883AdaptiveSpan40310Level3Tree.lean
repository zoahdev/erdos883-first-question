import Erdos883AdaptiveSpan40310Level3TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength40310_3 : adaptiveNumericSpans40310_3.length = 507 := by decide +kernel
theorem adaptiveSpanEvenCache40310_3 : adaptiveSpanEven40310_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain40310_3 : adaptiveSpanEven40310_3.domainCheck 20155 = true := by decide +kernel
theorem adaptiveSpanEvenEntries40310_3 : adaptiveSpanEven40310_3.spans = coreEvenSpans 20155 0 adaptiveNumericSpans40310_3 := by
  decide +kernel
theorem adaptiveSpanWholeCache40310_3 : adaptiveSpanWhole40310_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain40310_3 : adaptiveSpanWhole40310_3.domainCheck 20155 = true := by decide +kernel
theorem adaptiveSpanWholeEntries40310_3 : adaptiveSpanWhole40310_3.spans = coreWholeSpans 0 adaptiveNumericSpans40310_3 := by
  decide +kernel
end Erdos883Verified
