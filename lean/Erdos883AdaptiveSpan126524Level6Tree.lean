import Erdos883AdaptiveSpan126524Level6TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength126524_6 : adaptiveNumericSpans126524_6.length = 680 := by decide +kernel
theorem adaptiveSpanEvenCache126524_6 : adaptiveSpanEven126524_6.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain126524_6 : adaptiveSpanEven126524_6.domainCheck 63262 = true := by decide +kernel
theorem adaptiveSpanEvenEntries126524_6 : adaptiveSpanEven126524_6.spans = coreEvenSpans 63262 0 adaptiveNumericSpans126524_6 := by
  decide +kernel
theorem adaptiveSpanWholeCache126524_6 : adaptiveSpanWhole126524_6.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain126524_6 : adaptiveSpanWhole126524_6.domainCheck 63262 = true := by decide +kernel
theorem adaptiveSpanWholeEntries126524_6 : adaptiveSpanWhole126524_6.spans = coreWholeSpans 0 adaptiveNumericSpans126524_6 := by
  decide +kernel
end Erdos883Verified
