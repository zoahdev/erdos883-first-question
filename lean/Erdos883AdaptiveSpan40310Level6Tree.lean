import Erdos883AdaptiveSpan40310Level6TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength40310_6 : adaptiveNumericSpans40310_6.length = 507 := by decide +kernel
theorem adaptiveSpanEvenCache40310_6 : adaptiveSpanEven40310_6.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain40310_6 : adaptiveSpanEven40310_6.domainCheck 20155 = true := by decide +kernel
theorem adaptiveSpanEvenEntries40310_6 : adaptiveSpanEven40310_6.spans = coreEvenSpans 20155 0 adaptiveNumericSpans40310_6 := by
  decide +kernel
theorem adaptiveSpanWholeCache40310_6 : adaptiveSpanWhole40310_6.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain40310_6 : adaptiveSpanWhole40310_6.domainCheck 20155 = true := by decide +kernel
theorem adaptiveSpanWholeEntries40310_6 : adaptiveSpanWhole40310_6.spans = coreWholeSpans 0 adaptiveNumericSpans40310_6 := by
  decide +kernel
end Erdos883Verified
