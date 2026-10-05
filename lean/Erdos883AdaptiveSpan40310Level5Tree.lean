import Erdos883AdaptiveSpan40310Level5TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength40310_5 : adaptiveNumericSpans40310_5.length = 507 := by decide +kernel
theorem adaptiveSpanEvenCache40310_5 : adaptiveSpanEven40310_5.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain40310_5 : adaptiveSpanEven40310_5.domainCheck 20155 = true := by decide +kernel
theorem adaptiveSpanEvenEntries40310_5 : adaptiveSpanEven40310_5.spans = coreEvenSpans 20155 0 adaptiveNumericSpans40310_5 := by
  decide +kernel
theorem adaptiveSpanWholeCache40310_5 : adaptiveSpanWhole40310_5.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain40310_5 : adaptiveSpanWhole40310_5.domainCheck 20155 = true := by decide +kernel
theorem adaptiveSpanWholeEntries40310_5 : adaptiveSpanWhole40310_5.spans = coreWholeSpans 0 adaptiveNumericSpans40310_5 := by
  decide +kernel
end Erdos883Verified
