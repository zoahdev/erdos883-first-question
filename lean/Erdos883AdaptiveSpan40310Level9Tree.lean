import Erdos883AdaptiveSpan40310Level9TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength40310_9 : adaptiveNumericSpans40310_9.length = 507 := by decide +kernel
theorem adaptiveSpanEvenCache40310_9 : adaptiveSpanEven40310_9.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain40310_9 : adaptiveSpanEven40310_9.domainCheck 20155 = true := by decide +kernel
theorem adaptiveSpanEvenEntries40310_9 : adaptiveSpanEven40310_9.spans = coreEvenSpans 20155 0 adaptiveNumericSpans40310_9 := by
  decide +kernel
theorem adaptiveSpanWholeCache40310_9 : adaptiveSpanWhole40310_9.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain40310_9 : adaptiveSpanWhole40310_9.domainCheck 20155 = true := by decide +kernel
theorem adaptiveSpanWholeEntries40310_9 : adaptiveSpanWhole40310_9.spans = coreWholeSpans 0 adaptiveNumericSpans40310_9 := by
  decide +kernel
end Erdos883Verified
