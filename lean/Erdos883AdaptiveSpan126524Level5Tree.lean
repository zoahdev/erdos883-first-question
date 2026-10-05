import Erdos883AdaptiveSpan126524Level5TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength126524_5 : adaptiveNumericSpans126524_5.length = 680 := by decide +kernel
theorem adaptiveSpanEvenCache126524_5 : adaptiveSpanEven126524_5.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain126524_5 : adaptiveSpanEven126524_5.domainCheck 63262 = true := by decide +kernel
theorem adaptiveSpanEvenEntries126524_5 : adaptiveSpanEven126524_5.spans = coreEvenSpans 63262 0 adaptiveNumericSpans126524_5 := by
  decide +kernel
theorem adaptiveSpanWholeCache126524_5 : adaptiveSpanWhole126524_5.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain126524_5 : adaptiveSpanWhole126524_5.domainCheck 63262 = true := by decide +kernel
theorem adaptiveSpanWholeEntries126524_5 : adaptiveSpanWhole126524_5.spans = coreWholeSpans 0 adaptiveNumericSpans126524_5 := by
  decide +kernel
end Erdos883Verified
