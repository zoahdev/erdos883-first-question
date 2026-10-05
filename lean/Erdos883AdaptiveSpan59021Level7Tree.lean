import Erdos883AdaptiveSpan59021Level7TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength59021_7 : adaptiveNumericSpans59021_7.length = 555 := by decide +kernel
theorem adaptiveSpanEvenCache59021_7 : adaptiveSpanEven59021_7.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain59021_7 : adaptiveSpanEven59021_7.domainCheck 29511 = true := by decide +kernel
theorem adaptiveSpanEvenEntries59021_7 : adaptiveSpanEven59021_7.spans = coreEvenSpans 29511 0 adaptiveNumericSpans59021_7 := by
  decide +kernel
theorem adaptiveSpanWholeCache59021_7 : adaptiveSpanWhole59021_7.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain59021_7 : adaptiveSpanWhole59021_7.domainCheck 29511 = true := by decide +kernel
theorem adaptiveSpanWholeEntries59021_7 : adaptiveSpanWhole59021_7.spans = coreWholeSpans 0 adaptiveNumericSpans59021_7 := by
  decide +kernel
end Erdos883Verified
