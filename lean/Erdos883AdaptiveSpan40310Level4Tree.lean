import Erdos883AdaptiveSpan40310Level4TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength40310_4 : adaptiveNumericSpans40310_4.length = 507 := by decide +kernel
theorem adaptiveSpanEvenCache40310_4 : adaptiveSpanEven40310_4.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain40310_4 : adaptiveSpanEven40310_4.domainCheck 20155 = true := by decide +kernel
theorem adaptiveSpanEvenEntries40310_4 : adaptiveSpanEven40310_4.spans = coreEvenSpans 20155 0 adaptiveNumericSpans40310_4 := by
  decide +kernel
theorem adaptiveSpanWholeCache40310_4 : adaptiveSpanWhole40310_4.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain40310_4 : adaptiveSpanWhole40310_4.domainCheck 20155 = true := by decide +kernel
theorem adaptiveSpanWholeEntries40310_4 : adaptiveSpanWhole40310_4.spans = coreWholeSpans 0 adaptiveNumericSpans40310_4 := by
  decide +kernel
end Erdos883Verified
